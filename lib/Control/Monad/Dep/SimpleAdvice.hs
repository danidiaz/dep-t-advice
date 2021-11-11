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
{-# LANGUAGE BlockArguments #-}

-- | 
--    This module provides the 'Advice' datatype, along for functions for creating,
--    manipulating, composing and applying values of that type.
--
--    'Advice's are type-preserving transformations on effectful functions of
--    any number of arguments.
--
--    For example, assuming we have a record-of-functions like
--
-- >>> :{
--    data Env m = Env {
--      foo :: m ()
--    , bar :: Int -> m (Maybe Char)
--    , baz :: Int -> Bool -> m Char
--    } deriving Generic
--    env :: Env IO
--    env = Env {
--      foo = pure ()
--    , bar = \_ -> pure (Just 'c')
--    , baz = \_ _ -> pure 'i'
--    }
-- :}
--
-- We can modify all the functions in the record in this way:
--
-- >>> :{
--    env' :: Env IO
--    env' = env & advising (adviseRecord @_ @Top \_ -> printArgs stdout "prefix> ")
-- :}
--
-- or an individual function in this way:
--
-- >>> :{
--    env' :: Env IO
--    env' = env & advising \env -> env { 
--          bar = advise (printArgs stdout "prefix> ") (bar env)
--      } 
-- :}
--
-- __NOTE__:
--
-- This module is an alternative to "Control.Monad.Dep.Advice" with two advantages:
--
-- - It doesn't use 'Control.Monad.Dep.DepT'. The types are simpler because
--   they don't need to refer to 'Control.Monad.Dep.DepT''s environment.
--
-- - Unlike in "Control.Monad.Dep.Advice", we can advise components
--   which work on a fixed concrete monad like 'IO'.
--
-- Compared with "Control.Monad.Dep.Advice", it does require the extra step
-- of invoking the 'advising' helper function.
module Control.Monad.Dep.SimpleAdvice
  ( -- * Preparing components for being advised
    advising,
    AspectT (..),
    -- * The Advice type
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

    -- * Advising entire records
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
import Control.Monad.Dep.SimpleAdvice.Internal 

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
-- >>> import Control.Monad.Dep.SimpleAdvice
-- >>> import Control.Monad.Dep.SimpleAdvice.Basic (printArgs,returnMempty)
-- >>> import Control.Monad.Writer
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef
-- >>> import GHC.Generics (Generic)
-- >>> import GHC.Generics qualified
-- >>> import Data.Function


-- |
--    The most general (and complex) way of constructing 'Advice's.
--
--    An 'Advice' receives the arguments of the advised
--    function packed into an n-ary product 'NP', performs some 
--    effects based on them, and returns a potentially modified version of the 
--    arguments, along with a function for tweaking the execution of the
--    advised function.
--
-- >>> :{
--  doesNothing :: forall ca m r. Monad m => Advice ca m r
--  doesNothing = makeAdvice (\args -> pure (id, args)) 
-- :}
--
--
makeAdvice ::
  forall ca m r.
    ( forall as.
      All ca as =>
      NP I as ->
      AspectT m (AspectT m r -> AspectT m r, NP I as)
    ) ->
    Advice ca m r
makeAdvice = Advice

-- |
--    Create an advice which only tweaks and/or analyzes the function arguments.
--
-- >>> :{
--  doesNothing :: forall ca m r. Monad m => Advice ca m r
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
  makeAdvice $ \args -> do
    args' <- tweakArgs args
    pure (id, args')

-- |
--    Create an advice which only tweaks the execution of the final monadic action.
--
-- >>> :{
--  doesNothing :: forall ca m r. Monad m => Advice ca m r
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
makeExecutionAdvice tweakExecution = makeAdvice \args -> pure (tweakExecution, args)


-- | Apply an 'Advice' to some compatible function. The function must have its
-- effects in 'AspectT', and all of its arguments must satisfy the @ca@ constraint.
--
-- >>> :{
--  foo :: Int -> AspectT IO String
--  foo _ = pure "foo"
--  advisedFoo = advise (printArgs stdout "Foo args: ") foo
-- :}
--
-- __/TYPE APPLICATION REQUIRED!/__ If the @ca@ constraint of the 'Advice' remains polymorphic,
-- it must be supplied by means of a type application:
--
-- >>> :{
--  bar :: Int -> AspectT IO String
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
advise (Advice f) advisee = do
  let uncurried = multiuncurry @as @m @r advisee
      uncurried' args = do
        (tweakExecution, args') <- f args
        tweakExecution (uncurried args')
   in multicurry @as @m @r uncurried'

-- | This function \"installs\" an 'AspectT' newtype wrapper for the monad
-- parameter of a record-of-functions, applies some function on
-- the tweaked component, and then removes the wrapper from the result.
--
-- This is necessary because the typeclass machinery which handles
-- 'Advice's uses 'AspectT' as a \"mark\" to recognize \"the end of the function\".
advising 
    :: Coercible (r_ m) (r_ (AspectT m))
    => (r_ (AspectT m) -> r_ (AspectT m))
    -> r_ m -> r_ m
advising f = coerce . f . coerce

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
--  stricterPrintArgs :: forall m r. MonadIO m => Advice (Show `And` Eq `And` Ord) m r
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
restrictArgs evidence (Advice advice) = Advice \args ->
    let advice' :: forall as. All more as => NP I as -> AspectT m (AspectT m r -> AspectT m r, NP I as)
        advice' args' =
            case Data.SOP.Dict.mapAll @more @less evidence of
               f -> case f (Dict @(All more) @as) of
                        Dict -> advice args'
     in advice' args


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
