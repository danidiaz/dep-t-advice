{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Monad.Dep.SimpleAdvice
  ( -- * The Advice type
    Advice,

    -- * Creating Advice values
    makeAdvice,
    makeArgsAdvice,
    makeExecutionAdvice,

    -- * Applying Advices
    advise,

    -- * Harmonizing Advice argument constraints
    -- $restrict
    restrictArgs,

    -- * Advising and deceiving entire records
    -- $records
    adviseRecord,

    -- * "sop-core" re-exports
    -- $sop
    Top,
    And,
    All,
    NP (..),
    I (..),
    cfoldMap_NP,
    Dict (..),
  )
where

import Data.Coerce
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Dep.Has
import Data.Functor.Identity
import Data.Kind
import Data.List.NonEmpty qualified as N
import Data.SOP
import Data.SOP.Dict
import Data.SOP.NP
import Data.Typeable
import GHC.Generics qualified as G
import GHC.TypeLits
import Control.Applicative
import Control.Monad.Cont.Class
import Control.Monad.Error.Class
import Control.Monad.IO.Unlift
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Writer.Class
import Control.Monad.Zip

-- $setup
--
-- >>> :set -XTypeApplications
-- >>> :set -XStandaloneKindSignatures
-- >>> :set -XMultiParamTypeClasses
-- >>> :set -XFunctionalDependencies
-- >>> :set -XRankNTypes
-- >>> :set -XTypeOperators
-- >>> :set -XConstraintKinds
-- >>> :set -XNamedFieldPuns
-- >>> :set -XFlexibleContexts
-- >>> :set -XDerivingStrategies
-- >>> :set -XGeneralizedNewtypeDeriving
-- >>> :set -XDataKinds
-- >>> :set -XScopedTypeVariables
-- >>> :set -XDeriveGeneric
-- >>> :set -XImportQualifiedPost
-- >>> import Control.Monad
-- >>> import Control.Monad.Dep
-- >>> import Control.Monad.Dep.Advice
-- >>> import Control.Monad.Dep.Advice.Basic (printArgs,returnMempty)
-- >>> import Control.Monad.Writer
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef
-- >>> import GHC.Generics (Generic)
-- >>> import GHC.Generics qualified

-- | A generic transformation of 'AspectT'-effectful functions with environment
-- @e_@ of kind @(Type -> Type) -> Type@, base monad @m@ and return type @r@,
-- provided the functions satisfy certain constraint @ca@ of kind @Type ->
-- Constraint@ on all of their arguments.
--
-- Note that the type constructor for the environment @e_@ is given unapplied.
-- That is, @Advice Show NilEnv IO ()@ kind-checks but @Advice Show (NilEnv IO)
-- IO ()@ doesn't. See also 'Ensure'.
--
-- 'Advice's that don't care about the @ca@ constraint (because they don't
-- touch function arguments) can leave it polymorphic, and this facilitates
-- 'Advice' composition, but then the constraint must be given the catch-all
-- `Top` value (using a type application) at the moment of calling 'advise'.
--
-- See "Control.Monad.Dep.Advice.Basic" for examples.
type Advice ::
  (Type -> Constraint) ->
  (Type -> Type) ->
  Type ->
  Type
data Advice ca m r where
  Advice ::
    forall u ca m r.
    Proxy u ->
    ( forall as.
      All ca as =>
      NP I as ->
      AspectT m (u, NP I as)
    ) ->
    ( u ->
      AspectT m r ->
      AspectT m r
    ) ->
    Advice ca m r

type AspectT ::
  (Type -> Type) ->
  Type ->
  Type
newtype AspectT (m :: Type -> Type) (r :: Type) = AspectT {runAspectT :: m r}
  deriving
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadFix,
      MonadFail,
      MonadZip,
      MonadPlus,
      MonadCont,
      MonadIO,
      MonadUnliftIO
    )

instance MonadTrans AspectT where
  lift = AspectT 

deriving newtype instance MonadState s m => MonadState s (AspectT m)
deriving newtype instance MonadWriter w m => MonadWriter w (AspectT m)
deriving newtype instance MonadError e m => MonadError e (AspectT m)

-- |
--    'Advice's compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'AspectT' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Monad m => Semigroup (Advice ca m r) where
  Advice outer tweakArgsOuter tweakExecutionOuter <> Advice inner tweakArgsInner tweakExecutionInner =
    let captureExistentials ::
          forall ca r outer inner.
          Proxy outer ->
          ( forall as.
            All ca as =>
            NP I as ->
            AspectT m (outer, NP I as)
          ) ->
          ( outer ->
            AspectT m r ->
            AspectT m r
          ) ->
          Proxy inner ->
          ( forall as.
            All ca as =>
            NP I as ->
            AspectT m (inner, NP I as)
          ) ->
          ( inner ->
            AspectT m r ->
            AspectT m r
          ) ->
          Advice ca m r
        captureExistentials _ tweakArgsOuter' tweakExecutionOuter' _ tweakArgsInner' tweakExecutionInner' =
          Advice
            (Proxy @(Pair outer inner))
            ( let tweakArgs ::
                    forall as.
                    All ca as =>
                    NP I as ->
                    AspectT m (Pair outer inner, NP I as)
                  tweakArgs args =
                    do
                      (uOuter, argsOuter) <- tweakArgsOuter' @as args
                      (uInner, argsInner) <- tweakArgsInner' @as argsOuter
                      pure (Pair uOuter uInner, argsInner)
               in tweakArgs
            )
            ( let tweakExecution ::
                    Pair outer inner ->
                    AspectT m r ->
                    AspectT m r
                  tweakExecution =
                    ( \(Pair uOuter uInner) action ->
                        tweakExecutionOuter' uOuter (tweakExecutionInner' uInner action)
                    )
               in tweakExecution
            )
     in captureExistentials @ca outer tweakArgsOuter tweakExecutionOuter inner tweakArgsInner tweakExecutionInner

instance Monad m => Monoid (Advice ca m r) where
  mappend = (<>)
  mempty = Advice (Proxy @()) (\args -> pure (pure args)) (const id)

-- |
--    The most general (and complex) way of constructing 'Advice's.
--
--    'Advice's work in two phases. First, the arguments of the transformed
--    function are collected into an n-ary product 'NP', and passed to the
--    first argument of 'makeAdvice', which produces a (possibly transformed)
--    product of arguments, along with some summary value of type @u@. Use @()@
--    as the summary value if you don't care about it.
--
--    In the second phase, the monadic action produced by the function once all
--    arguments have been given is transformed using the second argument of
--    'makeAdvice'. This second argument also receives the summary value of
--    type @u@ calculated earlier.
--
-- >>> :{
--  doesNothing :: forall ca e_ m r. Monad m => Advice ca e_ m r
--  doesNothing = makeAdvice @() (\args -> pure (pure args)) (\() action -> action)
-- :}
--
--    __/TYPE APPLICATION REQUIRED!/__ When invoking 'makeAdvice', you must always give the
--    type of the existential @u@ through a type application. Otherwise you'll
--    get weird \"u is untouchable\" errors.
makeAdvice ::
  forall u ca m r.
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    AspectT m (u, NP I as)
  ) ->
  -- | The function that tweaks the execution.
  ( u ->
    AspectT m r ->
    AspectT m r
  ) ->
  Advice ca m r
makeAdvice = Advice (Proxy @u)

-- |
--    Create an advice which only tweaks and/or analyzes the function arguments.
--
--    Notice that there's no @u@ parameter, unlike with 'makeAdvice'.
--
-- >>> :{
--  doesNothing :: forall ca e_ m r. Monad m => Advice ca e_ m r
--  doesNothing = makeArgsAdvice pure
-- :}
makeArgsAdvice ::
  forall ca m r.
  Monad m =>
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    AspectT m (NP I as)
  ) ->
  Advice ca m r
makeArgsAdvice tweakArgs =
  makeAdvice @()
    ( \args -> do
        args <- tweakArgs args
        pure ((), args)
    )
    (const id)

-- |
--    Create an advice which only tweaks the execution of the final monadic action.
--
--    Notice that there's no @u@ parameter, unlike with 'makeAdvice'.
--
-- >>> :{
--  doesNothing :: forall ca e_ m r. Monad m => Advice ca e_ m r
--  doesNothing = makeExecutionAdvice id
-- :}
makeExecutionAdvice ::
  forall ca m r.
  Applicative m =>
  -- | The function that tweaks the execution.
  ( AspectT m r ->
    AspectT m r
  ) ->
  Advice ca m r
makeExecutionAdvice tweakExecution = makeAdvice @() (\args -> pure (pure args)) (\() action -> tweakExecution action)

data Pair a b = Pair !a !b

-- | Apply an 'Advice' to some compatible function. The function must have its
-- effects in 'AspectT', and all of its arguments must satisfy the @ca@ constraint.
--
-- >>> :{
--  foo :: Int -> AspectT NilEnv IO String
--  foo _ = pure "foo"
--  advisedFoo = advise (printArgs stdout "Foo args: ") foo
-- :}
--
-- __/TYPE APPLICATION REQUIRED!/__ If the @ca@ constraint of the 'Advice' remains polymorphic,
-- it must be supplied by means of a type application:
--
-- >>> :{
--  bar :: Int -> AspectT NilEnv IO String
--  bar _ = pure "bar"
--  advisedBar1 = advise (returnMempty @Top) bar
--  advisedBar2 = advise @Top returnMempty bar
-- :}
advise ::
  forall ca m r as advisee.
  (Multicurryable as m r advisee, All ca as, Monad m) =>
  -- | The advice to apply.
  Advice ca m r ->
  -- | A function to be adviced.
  advisee ->
  advisee
advise (Advice _ tweakArgs tweakExecution) advisee = do
  let uncurried = multiuncurry @as @m @r advisee
      uncurried' args = do
        (u, args') <- tweakArgs args
        tweakExecution u (uncurried args')
   in multicurry @as @m @r uncurried'

type Multicurryable ::
  [Type] ->
  (Type -> Type) ->
  Type ->
  Type ->
  Constraint
class Multicurryable as m r curried | curried -> as m r where
  multiuncurry :: curried -> NP I as -> AspectT m r
  multicurry :: (NP I as -> AspectT m r) -> curried

instance Monad m => Multicurryable '[] m r (AspectT m r) where
  multiuncurry action Nil = action
  multicurry f = f Nil

instance Multicurryable as m r curried => Multicurryable (a ': as) m r (a -> curried) where
  multiuncurry f (I a :* as) = multiuncurry @as @m @r @curried (f a) as
  multicurry f a = multicurry @as @m @r @curried (f . (:*) (I a))

-- $restrict
--
--    'Advice' values can be composed using the 'Monoid' instance, but only if
--    they have the same type parameters. It's unfortunate that—unlike with
--    normal function constraints—the @ca@ constraints of an 'Advice' aren't
--    automatically "collected" during composition.
--
--    Instead, we need to harmonize the @ca@ constraints of each 'Advice' by
--    turning them into the combination of all constraints. 'restrictArgs'
--    helps with that.
--
--    'restrictArgs' takes as parameter value-level "\evidence\" that one
--    constraint implies another. But how to construct such evidence? By using
--    the 'Dict' GADT, more precisely the deceptively simple-looking term
--    @\\Dict -> Dict@. That function "absorbs" some constraint present in the
--    ambient context and re-packages it a a new constraint that is implied by
--    the former. We can't rely on type inference here; we need to provide
--    enough type information to the GADT, be it as an explicit signature:
--
-- >>> :{
--  stricterPrintArgs :: forall e_ m r. MonadIO m => Advice (Show `And` Eq `And` Ord) e_ m r
--  stricterPrintArgs = restrictArgs (\Dict -> Dict) (printArgs stdout "foo")
-- :}
--
--    or with a type application to 'restrictArgs':
--
-- >>> stricterPrintArgs = restrictArgs @(Show `And` Eq `And` Ord) (\Dict -> Dict) (printArgs stdout "foo")

-- | Makes the constraint on the arguments more restrictive.
restrictArgs ::
  forall more less m r.
  -- | Evidence that one constraint implies the other. Every @x@ that has a @more@ instance also has a @less@ instance.
  (forall x. Dict more x -> Dict less x) ->
  -- | Advice with less restrictive constraint on the args.
  Advice less m r ->
  -- | Advice with more restrictive constraint on the args.
  Advice more m r
-- about the order of the type parameters... which is more useful?
-- A possible principle to follow:
-- We are likely to know the "less" constraint, because advices are likely to
-- come pre-packaged and having a type signature.
-- We arent' so sure about having a signature for a whole composed Advice,
-- because the composition might be done
-- on the fly, while constructing a record, without a top-level binding with a
-- type signature.  This seems to favor putting "more" first.
restrictArgs evidence (Advice proxy tweakArgs tweakExecution) =
  let captureExistential ::
        forall more less m r u.
        (forall x. Dict more x -> Dict less x) ->
        Proxy u ->
        ( forall as.
          All less as =>
          NP I as ->
          AspectT m (u, NP I as)
        ) ->
        ( u ->
          AspectT m r ->
          AspectT m r
        ) ->
        Advice more m r
      captureExistential evidence' _ tweakArgs' tweakExecution' =
        Advice
          (Proxy @u)
          ( let tweakArgs'' :: forall as. All more as => NP I as -> AspectT m (u, NP I as)
                tweakArgs'' = case Data.SOP.Dict.mapAll @more @less evidence' of
                  f -> case f (Dict @(All more) @as) of
                    Dict -> \args -> tweakArgs' @as args
             in tweakArgs''
          )
          tweakExecution'
   in captureExistential evidence proxy tweakArgs tweakExecution


-- advising *all* fields of a record
--
--
type AdvisedRecord :: (Type -> Constraint) -> (Type -> Type) -> (Type -> Constraint) -> ((Type -> Type) -> Type) -> Constraint
class AdvisedRecord ca m cr advised where
  _adviseRecord :: [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca m r) -> advised (AspectT m) -> advised (AspectT m)

type AdvisedProduct :: (Type -> Constraint) -> (Type -> Type) -> (Type -> Constraint) -> (k -> Type) -> Constraint
class AdvisedProduct ca m cr advised_ where
  _adviseProduct :: TypeRep -> [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca m r) -> advised_ k -> advised_ k

instance
  ( G.Generic (advised (AspectT m)),
    -- G.Rep (advised (AspectT m)) ~ G.D1 ('G.MetaData name mod p nt) (G.C1 y advised_),
    G.Rep (advised (AspectT m)) ~ G.D1 x (G.C1 y advised_),
    Typeable advised,
    AdvisedProduct ca m cr advised_
  ) =>
  AdvisedRecord ca m cr advised
  where
  _adviseRecord acc f unadvised =
    let G.M1 (G.M1 unadvised_) = G.from unadvised
        advised_ = _adviseProduct @_ @ca @m @cr (typeRep (Proxy @advised)) acc f unadvised_
     in G.to (G.M1 (G.M1 advised_))

instance
  ( AdvisedProduct ca m cr advised_left,
    AdvisedProduct ca m cr advised_right
  ) =>
  AdvisedProduct ca m cr (advised_left G.:*: advised_right)
  where
  _adviseProduct tr acc f (unadvised_left G.:*: unadvised_right) = _adviseProduct @_ @ca @m @cr tr acc f unadvised_left G.:*: _adviseProduct @_ @ca @m @cr tr acc f unadvised_right

data RecordComponent
  = Terminal
  | IWrapped
  | Recurse

type DiscriminateAdvisedComponent :: Type -> RecordComponent
type family DiscriminateAdvisedComponent c where
  DiscriminateAdvisedComponent (a -> b) = Terminal
  DiscriminateAdvisedComponent (AspectT m x) = Terminal
  DiscriminateAdvisedComponent (Identity _) = IWrapped
  DiscriminateAdvisedComponent (I _) = IWrapped
  DiscriminateAdvisedComponent _ = Recurse

type AdvisedComponent :: RecordComponent -> (Type -> Constraint) -> (Type -> Type) -> (Type -> Constraint) -> Type -> Constraint
class AdvisedComponent component_type ca m cr advised where
  _adviseComponent :: [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca m r) -> advised -> advised

instance
  ( AdvisedComponent (DiscriminateAdvisedComponent advised) ca m cr advised,
    KnownSymbol fieldName
  ) =>
  AdvisedProduct ca m cr (G.S1 ( 'G.MetaSel ( 'Just fieldName) su ss ds) (G.Rec0 advised))
  where
  _adviseProduct tr acc f (G.M1 (G.K1 advised)) =
    let acc' = acc ++ [(tr, symbolVal (Proxy @fieldName))]
     in G.M1 (G.K1 (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @m @cr acc' f advised))

instance
  AdvisedRecord ca m cr advisable =>
  AdvisedComponent Recurse ca m cr (advisable (AspectT m))
  where
  _adviseComponent acc f advised = _adviseRecord @ca @m @cr acc f advised

instance
  (Multicurryable as m r advised, All ca as, cr r, Monad m) =>
  AdvisedComponent Terminal ca m cr advised
  where
  _adviseComponent acc f advised = advise @ca @m (f acc) advised

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca m cr advised =>
  AdvisedComponent IWrapped ca m cr (Identity advised)
  where
  _adviseComponent acc f (Identity advised) = Identity (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @m @cr acc f advised)

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca m cr advised =>
  AdvisedComponent IWrapped ca m cr (I advised)
  where
  _adviseComponent acc f (I advised) = I (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @m @cr acc f advised)

-- | Gives 'Advice' to all the functions in a record-of-functions.
--
-- The function that builds the advice receives a list of tuples @(TypeRep, String)@
-- which represent the record types and fields names we have
-- traversed until arriving at the advised function. This info can be useful for
-- logging advices. It's a list instead of a single tuple because
-- 'adviseRecord' works recursively.
--
-- __/TYPE APPLICATION REQUIRED!/__ The @ca@ constraint on function arguments
-- and the @cr@ constraint on the result type must be supplied by means of a
-- type application. Supply 'Top' if no constraint is required.
adviseRecord ::
  forall ca cr m advised.
  AdvisedRecord ca m cr advised =>
  -- | The advice to apply.
  (forall r . cr r => [(TypeRep, String)] -> Advice ca m r) ->
  -- | The record to advise recursively.
  advised (AspectT m) ->
  -- | The advised record.
  advised (AspectT m)
adviseRecord = _adviseRecord @ca @m @cr []

-- $sop
-- Some useful definitions re-exported the from \"sop-core\" package.
--
-- 'NP' is an n-ary product used to represent the arguments of advised functions.
--
-- 'I' is an identity functor. The arguments processed by an 'Advice' come wrapped in it.
--
-- 'cfoldMap_NP' is useful to construct homogeneous lists out of the 'NP' product, for example:
--
-- >>> cfoldMap_NP (Proxy @Show) (\(I a) -> [show a]) (I False :* I (1::Int) :* Nil)
-- ["False","1"]

-- $constraints
--
-- Some useful definitions re-exported the from \"constraints\" package.
--
-- 'Dict' and '(:-)' are GADTs used to capture and transform constraints. Used in the 'restrictArgs' function.

-- $constrainthelpers
--
-- To help with the constraint @ca@ that parameterizes 'Advice', this library re-exports the following helpers from \"sop-core\":
--
-- * 'Top' is the \"always satisfied\" constraint, useful when whe don't want to require anything specific in @ca@.
--
-- * 'And' combines two constraints so that an 'Advice' can request them both, for example @Show \`And\` Eq@.
--
-- Also, the 'All' constraint says that some constraint is satisfied by all the
-- components of an 'NP' product. It's in scope when processing the function
-- arguments inside an 'Advice'.

-- $invocation
-- These functions are helpers for running 'AspectT' computations, beyond what 'runAspectT' provides.
--
-- They aren't directly related to 'Advice's, but they require some of the same machinery, and that's why they are here.
