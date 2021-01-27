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

-- |
--    This package provides the 'Advice' datatype, along for functions for creating,
--    manipulating, composing and applying values of that type.
--
--    'Advice's represent generic transformations on 'DepT'-effectful functions of
--    any number of arguments.
--
-- >>> :{
--    foo0 :: DepT NilEnv IO (Sum Int)
--    foo0 = pure (Sum 5)
--    foo1 :: Bool -> DepT NilEnv IO (Sum Int)
--    foo1 _ = foo0
--    foo2 :: Char -> Bool -> DepT NilEnv IO (Sum Int)
--    foo2 _ = foo1
-- :}
--
-- They work for @DepT@-actions of zero arguments:
--
-- >>> advise (printArgs stdout "foo0") foo0 `runDepT` NilEnv
-- foo0:
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- And for functions of one or more arguments, provided they end on a @DepT@-action:
--
-- >>> advise (printArgs stdout "foo1") foo1 False `runDepT` NilEnv
-- foo1: False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- >>> advise (printArgs stdout "foo2") foo2 'd' False `runDepT` NilEnv
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- 'Advice's can also tweak the result value of functions:
--
-- >>> advise (returnMempty @Top) foo2 'd' False `runDepT` NilEnv
-- Sum {getSum = 0}
--
-- And they can be combined using @Advice@'s 'Monoid' instance before being applied
-- (although that might require harmonizing their constraint parameters):
--
-- >>> advise (printArgs stdout "foo2" <> returnMempty) foo2 'd' False `runDepT` NilEnv
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 0}
module Control.Monad.Dep.Advice
  ( -- * The Advice type
    Advice,

    -- * Creating Advice values
    makeAdvice,
    makeArgsAdvice,
    makeExecutionAdvice,

    -- * Applying Advices
    advise,

    -- * Constraint helpers
    -- $constrainthelpers
    Ensure,

    -- * Harmonizing Advice argument constraints
    -- $restrict
    restrictArgs,

    -- * Invocation helpers
    -- $invocation
    runFinalDepT,
    runFromEnv,

    -- * "sop-core" re-exports
    -- $sop
    Top,
    And,
    All,
    NP (..),
    I (..),
    cfoldMap_NP,

    -- * "constraints" re-exports
    -- $constraints
    type (:-) (..),
    Dict (..),
  )
where

import Control.Monad.Dep
import Data.Constraint
import Data.Kind
import Data.SOP
import Data.SOP.Dict qualified as SOP
import Data.SOP.NP

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
-- >>> import Control.Monad
-- >>> import Control.Monad.Dep
-- >>> import Control.Monad.Dep.Advice
-- >>> import Control.Monad.Dep.Advice.Basic (printArgs,returnMempty)
-- >>> import Data.Constraint
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef

-- | A generic transformation of a 'DepT'-effectful function of any number of
-- arguments, provided the function satisfies certain constraints on the
-- arguments, the environment type constructor and base monad, and the return type.
--
-- It is parameterized by three constraints:
--
-- * @ca@ of kind @Type -> Constraint@, the constraint required of each argument (usually something like @Show@).
-- * @cem@ of kind @((Type -> Type) -> Type) -> (Type -> Type) -> Constraint@,
-- a two-place constraint required of the environment type constructor / base
-- monad combination. Note that the environment type constructor remains
-- unapplied. That is, for a given @cem@, @cem NilEnv IO@ kind-checks but @cem
-- (NilEnv IO) IO@ doesn't. See also 'Ensure'.
-- * @cr@ of kind @Type -> Constraint@, the constraint required of the return type.
--
-- We can define 'Advice's that work with concrete types by using 'MustBe' in
-- the case of @ca@ and @cr@, and 'MustBe2' in the case of @cem@.
--
-- 'Advice's that don't care about a particular constraint can leave it
-- polymorphic, and this facilitates composition, but the constraint must be
-- given some concrete value ('Top' in the case of @ca@ and @cr@, 'Top2' in
-- the case of @cem@) through type application at the moment of calling
-- 'advise'.
--
-- See "Control.Monad.Dep.Advice.Basic" for examples.
type Advice ::
  (Type -> Constraint) ->
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Type ->
  Type
data Advice ca e m r where
  Advice ::
    forall u ca e m r.
    Proxy u ->
    ( forall as.
      All ca as =>
      NP I as ->
      DepT e m (u, NP I as)
    ) ->
    ( 
      u ->
      DepT e m r ->
      DepT e m r
    ) ->
    Advice ca e m r

-- |
--    Aspects compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'DepT' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Monad m => Semigroup (Advice ca e m r) where
  Advice outer tweakArgsOuter tweakExecutionOuter <> Advice inner tweakArgsInner tweakExecutionInner =
    let captureExistentials ::
          forall ca e r outer inner.
          Proxy outer ->
          ( forall as.
            All ca as =>
            NP I as ->
            DepT e m (outer, NP I as)
          ) ->
          ( 
            outer ->
            DepT e m r ->
            DepT e m r
          ) ->
          Proxy inner ->
          ( forall as.
            All ca as =>
            NP I as ->
            DepT e m (inner, NP I as)
          ) ->
          ( 
            inner ->
            DepT e m r ->
            DepT e m r
          ) ->
          Advice ca e m r
        captureExistentials _ tweakArgsOuter' tweakExecutionOuter' _ tweakArgsInner' tweakExecutionInner' =
          Advice
            (Proxy @(Pair outer inner))
            ( let tweakArgs ::
                    forall as.
                    All ca as =>
                    NP I as ->
                    DepT e m (Pair outer inner, NP I as)
                  tweakArgs args =
                    do
                      (uOuter, argsOuter) <- tweakArgsOuter' @as args
                      (uInner, argsInner) <- tweakArgsInner' @as argsOuter
                      pure (Pair uOuter uInner, argsInner)
               in tweakArgs
            )
            ( let tweakExecution ::
                    Pair outer inner ->
                    DepT e m r ->
                    DepT e m r
                  tweakExecution =
                    ( \(Pair uOuter uInner) action ->
                        tweakExecutionOuter' uOuter (tweakExecutionInner' uInner action)
                    )
               in tweakExecution
            )
     in captureExistentials @ca @e outer tweakArgsOuter tweakExecutionOuter inner tweakArgsInner tweakExecutionInner

instance Monad m => Monoid (Advice ca e m r) where
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
--  doesNothing :: forall ca e m r. Monad m => Advice ca e m r
--  doesNothing = makeAdvice @() (\args -> pure (pure args)) (\() action -> action)
-- :}
--
--    __/IMPORTANT!/__ When invoking 'makeAdvice', you must always give the
--    type of the existential @u@ through a type application. Otherwise you'll
--    get weird \"u is untouchable\" errors.
makeAdvice ::
  forall u ca e m r.
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    DepT e m (u, NP I as)
  ) ->
  -- | The function that tweaks the execution.
  ( 
    u ->
    DepT e m r ->
    DepT e m r
  ) ->
  Advice ca e m r
makeAdvice = Advice (Proxy @u)

-- |
--    Create an advice which only tweaks and/or analyzes the function arguments.
--
--    Notice that there's no @u@ parameter, unlike with 'makeAdvice'.
--
-- >>> :{
--  doesNothing :: forall ca e m r. Monad m => Advice ca e m r
--  doesNothing = makeArgsAdvice pure
-- :}
makeArgsAdvice ::
  forall ca e m r.
  Monad m => 
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    DepT e m (NP I as)
  ) ->
  Advice ca e m r
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
--  doesNothing :: forall ca e m r. Monad m => Advice ca e m r
--  doesNothing = makeExecutionAdvice id
-- :}
makeExecutionAdvice ::
  forall ca e m r.
  Applicative m =>
  -- | The function that tweaks the execution.
  ( 
    DepT e m r ->
    DepT e m r
  ) ->
  Advice ca e m r
makeExecutionAdvice tweakExecution = makeAdvice @() (\args -> pure (pure args)) (\() action -> tweakExecution action)

data Pair a b = Pair !a !b

-- |
-- 'Ensure' is a helper for lifting typeclass definitions of the form:
--
-- >>> :{
--  type HasLogger :: Type -> (Type -> Type) -> Constraint
--  class HasLogger em m | em -> m where
--    logger :: em -> String -> m ()
-- :}
--
-- To work as the @cem@ constraint, like this:
--
-- XXXXXXXXXXXXXXXXXXXX
--
-- Why is it necessary? Two-place @HasX@-style constraints receive the \"fully
-- applied\" type of the record-of-functions. That is: @NilEnv IO@ instead of
-- simply @NilEnv@. This allows them to also work with monomorphic
-- environments (like those in <http://hackage.haskell.org/package/rio RIO>) whose type isn't parameterized by any monad.
--
-- But the @cem@ constraint works with the type constructor of the environment
-- record, of kind @(Type -> Type) -> Type@, and not with the fully applied
-- type of kind @Type@.
type Ensure :: (Type -> (Type -> Type) -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
type Ensure c e m = c (e (DepT e m)) (DepT e m) 

-- | Apply an 'Advice' to some compatible function. The function must have its
-- effects in 'DepT', and satisfy the constraints required by the 'Advice'.
--
-- __/IMPORTANT!/__ If the @ca@, @cem@ or @cr@ constraints of the supplied
-- 'Advice' remain polymorphic, they must be given types by means of type
-- applications:
--
-- >>> :{
--  foo :: Int -> DepT NilEnv IO String
--  foo _ = pure "foo"
--  advisedFoo1 = advise (returnMempty @Top) foo
--  advisedFoo2 = advise @Top returnMempty foo
--  advisedFoo3 = advise (printArgs stdout "args: ") foo
-- :}
advise ::
  forall ca e m r as advisee.
  (Multicurryable as e m r advisee, All ca as, Monad m) =>
  -- | The advice to apply.
  Advice ca e m r ->
  -- | A function to be adviced.
  advisee ->
  advisee
advise (Advice _ tweakArgs tweakExecution) advisee = do
  let uncurried = multiuncurry @as @e @m @r advisee
      uncurried' args = do
        (u, args') <- tweakArgs args
        tweakExecution u (uncurried args')
   in multicurry @as @e @m @r uncurried'

type Multicurryable ::
  [Type] ->
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Type ->
  Type ->
  Constraint
class Multicurryable as e m r curried | curried -> as e m r where
  type DownToBaseMonad as e m r curried :: Type
  multiuncurry :: curried -> NP I as -> DepT e m r
  multicurry :: (NP I as -> DepT e m r) -> curried
  _runFromEnv :: m (e (DepT e m)) -> (e (DepT e m) -> curried) -> DownToBaseMonad as e m r curried

instance Monad m => Multicurryable '[] e m r (DepT e m r) where
  type DownToBaseMonad '[] e m r (DepT e m r) = m r
  multiuncurry action Nil = action
  multicurry f = f Nil
  _runFromEnv producer extractor = do
    e <- producer
    runDepT (extractor e) e

instance Multicurryable as e m r curried => Multicurryable (a ': as) e m r (a -> curried) where
  type DownToBaseMonad (a ': as) e m r (a -> curried) = a -> DownToBaseMonad as e m r curried
  multiuncurry f (I a :* as) = multiuncurry @as @e @m @r @curried (f a) as
  multicurry f a = multicurry @as @e @m @r @curried (f . (:*) (I a))
  _runFromEnv producer extractor a = _runFromEnv @as @e @m @r @curried producer (\f -> extractor f a)

-- | Given a base monad @m@ action that gets hold of the 'DepT' environment, run
-- the 'DepT' transformer at the tip of a curried function.
--
-- >>> :{
--  foo :: Int -> Int -> Int -> DepT NilEnv IO ()
--  foo _ _ _ = pure ()
-- :}
--
--  >>> runFinalDepT (pure NilEnv) foo 1 2 3 :: IO ()
runFinalDepT ::
  forall as e m r curried.
  Multicurryable as e m r curried =>
  -- | action that gets hold of the environment
  m (e (DepT e m)) ->
  -- | function to invoke with effects in 'DepT'
  curried ->
  -- | a new function with effects in the base monad
  DownToBaseMonad as e m r curried
runFinalDepT producer extractor = _runFromEnv producer (const extractor)

-- | Given a base monad @m@ action that gets hold of the 'DepT' environment,
-- and a function capable of extracting a curried function from the
-- environment, run the 'DepT' transformer at the tip of the resulting curried
-- function.
--
-- Why put the environment behind the @m@ action? Well, since getting to the
-- end of the curried function takes some work, it's a good idea to have some
-- flexibility once we arrive there. For example, the environment could be
-- stored in a "Data.IORef" and change in response to events, perhaps with
-- advices being added or removed.
--
-- >>> :{
--   type MutableEnv :: (Type -> Type) -> Type
--   data MutableEnv m = MutableEnv { _foo :: Int -> m (Sum Int) }
--   :}
--
-- >>> :{
--   do envRef <- newIORef (MutableEnv (pure . Sum))
--      let foo' = runFromEnv (readIORef envRef) _foo
--      do r <- foo' 7
--         print r
--      modifyIORef envRef (\e -> e { _foo = advise @Top returnMempty (_foo e) })
--      do r <- foo' 7
--         print r
-- :}
-- Sum {getSum = 7}
-- Sum {getSum = 0}
runFromEnv ::
  forall as e m r curried.
  Multicurryable as e m r curried =>
  -- | action that gets hold of the environment
  m (e (DepT e m)) ->
  -- | gets a function from the environment with effects in 'DepT'
  (e (DepT e m) -> curried) ->
  -- | a new function with effects in the base monad
  DownToBaseMonad as e m r curried
runFromEnv = _runFromEnv

-- $restrict
--
--    'Advice' values can be composed using the 'Monoid' instance, but only if
--    the have the same constraint parameters. It's unfortunate that—unlike with
--    normal functions—'Advice' constaints aren't automatically "collected"
--    during composition.
--
--    We need to harmonize the constraints on each 'Advice' by turning them
--    into the combination of all constraints. The functions in this section
--    help with that.
--
--    These functions take as parameter evidence of entailment between
--    constraints, using the type '(:-)' from the \"constraints\" package.  But
--    how to construct such evidence? By using the 'Sub' and the 'Dict'
--    constructors, with either an explicit type signature:
--
--    XXXXXXXXXXXXXXXXXXXXXX


-- | Makes the constraint on the arguments more restrictive.
restrictArgs ::
  forall more less e m r.
  -- | Evidence that one constraint implies the other.
  (forall x. more x :- less x) ->
  -- | Advice with less restrictive constraint on the args.
  Advice less e m r ->
  -- | Advice with more restrictive constraint on the args.
  Advice more e m r
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
        forall more less e m r u.
        (forall x. more x :- less x) ->
        Proxy u ->
        ( forall as.
          All less as =>
          NP I as ->
          DepT e m (u, NP I as)
        ) ->
        ( 
          u ->
          DepT e m r ->
          DepT e m r
        ) ->
        Advice more e m r
      captureExistential evidence' _ tweakArgs' tweakExecution' =
        Advice
          (Proxy @u)
          ( let tweakArgs'' :: forall as. All more as => NP I as -> DepT e m (u, NP I as)
                tweakArgs'' = case SOP.mapAll @more @less (translateEvidence @more @less evidence') of
                  f -> case f (SOP.Dict @(All more) @as) of
                    SOP.Dict -> \args -> tweakArgs' @as args
             in tweakArgs''
          )
          tweakExecution'
   in captureExistential evidence proxy tweakArgs tweakExecution


translateEvidence :: forall more less a. (forall x. more x :- less x) -> SOP.Dict more a -> SOP.Dict less a
translateEvidence evidence SOP.Dict =
  case evidence @a of
    Sub Dict -> SOP.Dict @less @a

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
-- Some  <https://www.reddit.com/r/haskell/comments/ab8ypl/monthly_hask_anything_january_2019/edk1ot3/ class synonyms>
-- to help create the constraints that parameterize the 'Advice' type.
--
-- This library also re-exports the 'Top', 'And' and 'All' helpers from \"sop-core\":
--
-- * 'Top' is the \"always satisfied\" constraint, useful when whe don't want to require anything specific in @ca@ or @cr@ (@cem@ requires 'Top2').
--
-- * 'And' combines constraints for @ca@ or @cr@ (@cem@ requires 'And2').
--
-- * 'All' says that some constraint is satisfied by all the components of an 'NP'
-- product. In this library, it's used to stipulate constraints on the
-- arguments of advised functions.

-- $invocation
-- These functions are helpers for running 'DepT' computations, beyond what 'runDepT' provides.
--
-- They aren't directly related to 'Advice's, but they require some of the same machinery, and that's why they are here.
