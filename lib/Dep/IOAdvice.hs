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
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}

-- |
--    This module provides the 'Advice' datatype, along for functions for creating,
--    manipulating, composing and applying values of that type.
--
--    'Advice's are type-preserving transformations on 'IO'-effectful functions of
--    any number of arguments.
--
-- >>> :{
--    foo0 :: IO (Sum Int)
--    foo0 = pure (Sum 5)
--    foo1 :: Bool -> IO (Sum Int)
--    foo1 _ = foo0
--    foo2 :: Char -> Bool -> IO (Sum Int)
--    foo2 _ = foo1
-- :}
--
-- They work for @IO@-actions of zero arguments:
--
-- >>> advise (printArgs stdout "foo0") foo0 
-- foo0:
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- And for functions of one or more arguments, provided they end on a @IO@-action:
--
-- >>> advise (printArgs stdout "foo1") foo1 False
-- foo1: False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- >>> advise (printArgs stdout "foo2") foo2 'd' False
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- 'Advice's can also tweak the result value of functions:
--
-- >>> advise (returnMempty @Top) foo2 'd' False
-- Sum {getSum = 0}
--
-- And they can be combined using @Advice@'s 'Monoid' instance before being
-- applied:
--
-- >>> advise (printArgs stdout "foo2" <> returnMempty) foo2 'd' False
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 0}
--
-- Although sometimes composition might require harmonizing the constraints
-- each 'Advice' places on the arguments, if they differ.
module Dep.IOAdvice
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
    Dict (..)
  )
where

import Dep.Has
import Dep.Env
import Data.Functor.Identity
import Data.Kind
import Data.List.NonEmpty qualified as N
import Data.List.NonEmpty (NonEmpty)
import Data.SOP
import Data.SOP.Dict
import Data.SOP.NP
import Data.Typeable
import GHC.Generics qualified as G
import GHC.TypeLits
import Data.Coerce
import Data.Bifunctor (first)

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
-- >>> import Dep.IOAdvice
-- >>> import Dep.IOAdvice.Basic (printArgs,returnMempty)
-- >>> import Control.Monad
-- >>> import Control.Monad.Reader
-- >>> import Control.Monad.Writer
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef
-- >>> import Data.Function ((&))
-- >>> import GHC.Generics (Generic)
-- >>> import GHC.Generics qualified


-- | A generic transformation of 'IO'-effectful functions of return type @r@,
-- provided the functions satisfy certain constraint @ca@ on all of their
-- arguments.
--
-- 'Advice's that don't care about the @ca@ constraint (because they don't
-- touch function arguments) can leave it polymorphic, and this facilitates
-- 'Advice' composition, but then the constraint must be given the catch-all
-- `Top` value (using a type application) at the moment of calling 'advise'.
--
-- See "Dep.IOAdvice.Basic" for examples.
type Advice ::
  (Type -> Constraint) ->
  Type ->
  Type
data Advice (ca :: Type -> Constraint) r where
  Advice ::
    forall ca r.
    ( forall as.
      All ca as =>
      NP I as ->
      IO (IO r -> IO r, NP I as)
    ) ->
    Advice ca r

-- |
--    'Advice's compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'IO' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Semigroup (Advice ca r) where
  Advice outer <> Advice inner = Advice \args -> do
    (tweakOuter, argsOuter) <- outer args
    (tweakInner, argsInner) <- inner argsOuter
    pure (tweakOuter . tweakInner, argsInner)

instance Monoid (Advice ca r) where
  mappend = (<>)
  mempty = Advice \args -> pure (id, args)

-- |
--    The most general way of constructing 'Advice's.
--
--    An 'Advice' is a function that transforms other functions in an 
--    arity-polymorphic way. It receives the arguments of the advised
--    function packed into an n-ary product 'NP', performs some 
--    effects based on them, and returns a potentially modified version of the 
--    arguments, along with a function for tweaking the execution of the
--    advised function.
--
-- >>> :{
--  doesNothing :: forall ca r. Advice ca r
--  doesNothing = makeAdvice (\args -> pure (id,  args)) 
-- :}
--
--
makeAdvice ::
  forall ca r.
  -- | The function that tweaks the arguments and the execution.
  ( forall as.
    All ca as =>
    NP I as ->
    IO (IO r -> IO r, NP I as)
  ) ->
  Advice ca r
makeAdvice = Advice

-- |
--    Create an advice which only tweaks and/or analyzes the function arguments.
--
-- >>> :{
--  doesNothing :: forall ca r. Advice ca r
--  doesNothing = makeArgsAdvice pure
-- :}
makeArgsAdvice ::
  forall ca r.
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    IO (NP I as)
  ) ->
  Advice ca r
makeArgsAdvice tweakArgs =
  makeAdvice $ \args -> do
    args' <- tweakArgs args
    pure (id, args')

-- |
--    Create an advice which only tweaks the execution of the final monadic action.
--
-- >>> :{
--  doesNothing :: forall ca r. Advice ca r
--  doesNothing = makeExecutionAdvice id
-- :}
makeExecutionAdvice ::
  forall ca r.
  -- | The function that tweaks the execution.
  ( IO r ->
    IO r
  ) ->
  Advice ca r
makeExecutionAdvice tweakExecution = makeAdvice \args -> pure (tweakExecution, args)

data Pair a b = Pair !a !b

-- | Apply an 'Advice' to some compatible function. The function must have its
-- effects in 'IO', and all of its arguments must satisfy the @ca@ constraint.
--
-- >>> :{
--  foo :: Int -> IO String
--  foo _ = pure "foo"
--  advisedFoo = advise (printArgs stdout "Foo args: ") foo
-- :}
--
-- __/TYPE APPLICATION REQUIRED!/__ If the @ca@ constraint of the 'Advice' remains polymorphic,
-- it must be supplied by means of a type application:
--
-- >>> :{
--  bar :: Int -> IO String
--  bar _ = pure "bar"
--  advisedBar1 = advise (returnMempty @Top) bar
--  advisedBar2 = advise @Top returnMempty bar
-- :}
advise ::
  forall ca r as advisee.
  (Multicurryable as r advisee, All ca as) =>
  -- | The advice to apply.
  Advice ca r ->
  -- | A function to be adviced.
  advisee ->
  advisee
advise (Advice f) advisee =
  let uncurried = multiuncurry @as @r advisee
      uncurried' args = do
        (tweakExecution, args') <- f args
        tweakExecution (uncurried args')
   in multicurry @as @r uncurried'

type Multicurryable ::
  [Type] ->
  Type ->
  Type ->
  Constraint
class Multicurryable as r curried | curried -> as r where
  multiuncurry :: curried -> NP I as -> IO r
  multicurry :: (NP I as -> IO r) -> curried

instance Multicurryable '[] r (IO r) where
  multiuncurry :: IO r -> NP I '[] -> IO r
  multiuncurry action Nil = action
  multicurry f = f Nil

instance (Multicurryable as r curried) => Multicurryable (a ': as) r (a -> curried) where
  multiuncurry f (I a :* as) = multiuncurry @as @r @curried (f a) as
  multicurry f a = multicurry @as @r @curried (f . (:*) (I a))

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
--  stricterPrintArgs :: forall r. Advice (Show `And` Eq `And` Ord) r
--  stricterPrintArgs = restrictArgs (\Dict -> Dict) (printArgs stdout "foo")
-- :}
--
--    or with a type application to 'restrictArgs':
--
-- >>> stricterPrintArgs = restrictArgs @(Show `And` Eq `And` Ord) (\Dict -> Dict) (printArgs stdout "foo")

-- | Makes the constraint on the arguments more restrictive.
restrictArgs ::
  forall more less r.
  -- | Evidence that one constraint implies the other. Every @x@ that has a @more@ instance also has a @less@ instance.
  (forall x. Dict more x -> Dict less x) ->
  -- | Advice with less restrictive constraint on the args.
  Advice less r ->
  -- | Advice with more restrictive constraint on the args.
  Advice more r
-- about the order of the type parameters... which is more useful?
-- A possible principle to follow:
-- We are likely to know the "less" constraint, because advices are likely to
-- come pre-packaged and having a type signature.
-- We arent' so sure about having a signature for a whole composed Advice,
-- because the composition might be done
-- on the fly, while constructing a record, without a top-level binding with a
-- type signature.  This seems to favor putting "more" first.
restrictArgs evidence (Advice advice) = Advice \args ->
    let advice' :: forall as. All more as => NP I as -> IO (IO r -> IO r, NP I as)
        advice' args' =
            case Data.SOP.Dict.mapAll @more @less evidence of
               f -> case f (Dict @(All more) @as) of
                        Dict -> advice args'
     in advice' args


data RecordComponent
  = Terminal
  | IWrapped
  | Recurse

-- advising *all* fields of a record
--
--
type AdvisedRecord :: (Type -> Constraint) -> (Type -> Constraint) -> ((Type -> Type) -> Type) -> Constraint
class AdvisedRecord ca cr advised where
  _adviseRecord :: [(TypeRep, String)] -> (forall r. cr r => NonEmpty (TypeRep, String) -> Advice ca r) -> advised IO -> advised IO

type AdvisedProduct :: (Type -> Constraint) -> (Type -> Constraint) -> (k -> Type) -> Constraint
class AdvisedProduct ca cr advised_ where
  _adviseProduct :: TypeRep -> [(TypeRep, String)] -> (forall r. cr r => NonEmpty (TypeRep, String) -> Advice ca r) -> advised_ k -> advised_ k

instance
  ( G.Generic (advised IO),
    G.Rep (advised IO) ~ G.D1 x (G.C1 y advised_),
    Typeable advised,
    AdvisedProduct ca cr advised_
  ) =>
  AdvisedRecord ca cr advised
  where
  _adviseRecord acc f unadvised =
    let G.M1 (G.M1 unadvised_) = G.from unadvised
        advised_ = _adviseProduct @_ @ca @cr (typeRep (Proxy @advised)) acc f unadvised_
     in G.to (G.M1 (G.M1 advised_))

instance
  ( AdvisedProduct ca cr advised_left,
    AdvisedProduct ca cr advised_right
  ) =>
  AdvisedProduct ca cr (advised_left G.:*: advised_right)
  where
  _adviseProduct tr acc f (unadvised_left G.:*: unadvised_right) = _adviseProduct @_ @ca @cr tr acc f unadvised_left G.:*: _adviseProduct @_ @ca @cr tr acc f unadvised_right

type DiscriminateAdvisedComponent :: Type -> RecordComponent
type family DiscriminateAdvisedComponent c where
  DiscriminateAdvisedComponent (_ -> _) = 'Terminal
  DiscriminateAdvisedComponent (IO _) = 'Terminal
  DiscriminateAdvisedComponent (Identity _) = 'IWrapped
  DiscriminateAdvisedComponent (I _) = 'IWrapped
  DiscriminateAdvisedComponent _ = 'Recurse

type AdvisedComponent :: RecordComponent -> (Type -> Constraint) -> (Type -> Constraint) -> Type -> Constraint
class AdvisedComponent component_type ca cr advised where
  _adviseComponent :: [(TypeRep, String)] -> (forall r. cr r => NonEmpty (TypeRep, String) -> Advice ca r) -> advised -> advised

instance
  ( AdvisedComponent (DiscriminateAdvisedComponent advised) ca cr advised,
    KnownSymbol fieldName
  ) =>
  AdvisedProduct ca cr (G.S1 ( 'G.MetaSel ( 'Just fieldName) su ss ds) (G.Rec0 advised))
  where
  _adviseProduct tr acc f (G.M1 (G.K1 advised)) =
    let acc' = (tr, symbolVal (Proxy @fieldName)) : acc
     in G.M1 (G.K1 (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @cr acc' f advised))

instance
  (Multicurryable as r advised, All ca as, cr r) =>
  AdvisedComponent 'Terminal ca cr advised
  where
  _adviseComponent acc f advised = advise @ca (f (N.fromList acc)) advised

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca cr advised =>
  AdvisedComponent 'IWrapped ca cr (Identity advised)
  where
  _adviseComponent acc f (Identity advised) = Identity (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @cr acc f advised)

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca cr advised =>
  AdvisedComponent 'IWrapped ca cr (I advised)
  where
  _adviseComponent acc f (I advised) = I (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @cr acc f advised)

instance
  AdvisedRecord ca cr advisable =>
  AdvisedComponent 'Recurse ca cr (advisable IO)
  where
  _adviseComponent acc f advised = _adviseRecord @ca @cr acc f advised


-- | Gives 'Advice' to all the functions in a record-of-functions.
--
-- The function that builds the advice receives a list of tuples @(TypeRep, String)@
-- which represent the record types and fields names we have
-- traversed until arriving at the advised function. This info can be useful for
-- logging advices. It's a list instead of a single tuple because
-- 'adviseRecord' works recursively. The elements come innermost-first.
--
-- __/TYPE APPLICATION REQUIRED!/__ The @ca@ constraint on function arguments
-- and the @cr@ constraint on the result type must be supplied by means of a
-- type application. Supply 'Top' if no constraint is required.
adviseRecord ::
  forall ca cr advised.
  AdvisedRecord ca cr advised =>
  -- | The advice to apply.
  (forall r . cr r => NonEmpty (TypeRep, String) -> Advice ca r) ->
  -- | The record to advise recursively.
  advised IO ->
  -- | The advised record.
  advised IO
adviseRecord = _adviseRecord @ca @cr []

-- $records
--
-- 'adviseRecord' is a version of 'advise' that, instead of working on bare
-- functions, transforms entire records-of-functions in one go. It also works
-- with newtypes containing a single function. The records must derive 'GHC.Generics.Generic'.
--
-- Useful with the \"wrapped\" style of components facilitated by @Control.Monad.Dep.Has@.
--
-- >>> :{
--   type Logger :: (Type -> Type) -> Type
--   newtype Logger d = Logger {log :: String -> d ()} deriving Generic
--   type Repository :: (Type -> Type) -> Type
--   data Repository d = Repository
--     { select :: String -> d [Int],
--       insert :: [Int] -> d ()
--     } deriving Generic
--   type Controller :: (Type -> Type) -> Type
--   newtype Controller d = Controller {serve :: Int -> d String} deriving Generic
--   type Env :: (Type -> Type) -> Type
--   data Env m = Env
--     { logger :: Logger m,
--       repository :: Repository m,
--       controller :: Controller m
--     }
--   env :: Env IO
--   env =
--     let logger = Logger \_ -> pure ()
--         repository =
--           Repository {select = \_ -> pure [], insert = \_ -> pure ()} &
--           adviseRecord @Top @Top mempty 
--         controller =
--           Controller { serve = \_ -> pure "view" } &
--           adviseRecord @Top @Top mempty 
--      in Env {logger, repository, controller}
-- :}

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
