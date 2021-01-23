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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE PolyKinds #-}

-- |
--    This package provices the 'Advice' datatype, along for functions for creating,
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
-- >>> :{
--    let action = advise (printArgs @Top stdout "foo0") foo0
--     in runDepT action NilEnv
-- :}
-- foo0:
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- And for functions of one or more arguments, provided they end on a @DepT@-action:
--
-- >>> :{
--    let action = advise (printArgs @Top stdout "foo1") foo1 False
--     in runDepT action NilEnv
-- :}
-- foo1: False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- >>> :{
--    let action = advise (printArgs @Top stdout "foo2") foo2 'd' False
--     in runDepT action NilEnv
-- :}
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- 'Advice's can also tweak the result value of functions:
--
-- >>> :{
--    let action = advise (returnMempty @Top @Top2) foo2 'd' False
--     in runDepT action NilEnv
-- :}
-- Sum {getSum = 0}
--
-- And they can be combined using @Advice@'s 'Monoid' instance before being applied
-- (although that might require harmonizing their constraint parameters):
--
-- >>> :{
--    let action = advise (printArgs stdout "foo2" <> returnMempty) foo2 'd' False
--     in runDepT action NilEnv
-- :}
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
    Top2,
    And2,
    MonadConstraint,
    EnvConstraint,
    MustBe,
    MustBe2,

    -- * Combining Advices by harmonizing their constraints
    -- $restrict
    restrictArgs,
    restrictEnv,
    restrictResult,

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
-- >>> :set -XTypeApplications -XStandaloneKindSignatures -XMultiParamTypeClasses -XFunctionalDependencies -XRankNTypes -XTypeOperators -XConstraintKinds
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
  (((Type -> Type) -> Type) -> (Type -> Type) -> Constraint) ->
  (Type -> Constraint) ->
  Type
data Advice ca cem cr where
  Advice ::
    forall u ca cem cr.
    Proxy u ->
    ( forall as e m.
      (All ca as, cem e m, Monad m) =>
      NP I as ->
      DepT e m (u, NP I as)
    ) ->
    ( forall e m r.
      (cem e m, Monad m, cr r) =>
      u ->
      DepT e m r ->
      DepT e m r
    ) ->
    Advice ca cem cr

-- |
--    Aspects compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'DepT' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Semigroup (Advice ca cem cr) where
  Advice outer tweakArgsOuter tweakExecutionOuter <> Advice inner tweakArgsInner tweakExecutionInner =
    let captureExistentials ::
          forall ca cem cr outer inner.
          Proxy outer ->
          ( forall as e m.
            (All ca as, cem e m, Monad m) =>
            NP I as ->
            DepT e m (outer, NP I as)
          ) ->
          ( forall e m r.
            (cem e m, Monad m, cr r) =>
            outer ->
            DepT e m r ->
            DepT e m r
          ) ->
          Proxy inner ->
          ( forall as e m.
            (All ca as, cem e m, Monad m) =>
            NP I as ->
            DepT e m (inner, NP I as)
          ) ->
          ( forall e m r.
            (cem e m, Monad m, cr r) =>
            inner ->
            DepT e m r ->
            DepT e m r
          ) ->
          Advice ca cem cr
        captureExistentials _ tweakArgsOuter' tweakExecutionOuter' _ tweakArgsInner' tweakExecutionInner' =
          Advice
            (Proxy @(Pair outer inner))
            ( let tweakArgs ::
                    forall as e m.
                    (All ca as, cem e m, Monad m) =>
                    NP I as ->
                    DepT e m (Pair outer inner, NP I as)
                  tweakArgs args =
                    do
                      (uOuter, argsOuter) <- tweakArgsOuter' @as @e @m args
                      (uInner, argsInner) <- tweakArgsInner' @as @e @m argsOuter
                      pure (Pair uOuter uInner, argsInner)
               in tweakArgs
            )
            ( let tweakExecution ::
                    forall e m r.
                    (cem e m, Monad m, cr r) =>
                    Pair outer inner ->
                    DepT e m r ->
                    DepT e m r
                  tweakExecution =
                    ( \(Pair uOuter uInner) action ->
                        tweakExecutionOuter' @e @m @r uOuter (tweakExecutionInner' @e @m @r uInner action)
                    )
               in tweakExecution
            )
     in captureExistentials @ca @cem @cr outer tweakArgsOuter tweakExecutionOuter inner tweakArgsInner tweakExecutionInner

instance Monoid (Advice ca cem cr) where
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
--  doesNothing :: forall ca cem cr. Advice ca cem cr
--  doesNothing = makeAdvice @() (\args -> pure (pure args)) (\() action -> action)
-- :}
--
--    __/IMPORTANT!/__ When invoking 'makeAdvice', you must always give the
--    type of the existential @u@ through a type application. Otherwise you'll
--    get weird \"u is untouchable\" errors.
--
makeAdvice ::
  forall u ca cem cr.
  -- | The function that tweaks the arguments.
  ( forall as e m.
    (All ca as, cem e m, Monad m) =>
    NP I as ->
    DepT e m (u, NP I as)
  ) ->
  -- | The function that tweaks the execution.
  ( forall e m r.
    (cem e m, Monad m, cr r) =>
    u ->
    DepT e m r ->
    DepT e m r
  ) ->
  Advice ca cem cr
makeAdvice = Advice (Proxy @u)

-- |
--    Create an advice which only tweaks and/or analyzes the function arguments.
--
--    Notice that there's no @u@ parameter, unlike with 'makeAdvice'.
--
-- >>> :{ 
--  doesNothing :: forall ca cem cr. Advice ca cem cr
--  doesNothing = makeArgsAdvice pure 
-- :}
--
makeArgsAdvice ::
  forall ca cem cr.
  -- | The function that tweaks the arguments.
  ( forall as e m.
    (All ca as, cem e m, Monad m) =>
    NP I as ->
    DepT e m (NP I as)
  ) ->
  Advice ca cem cr
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
--  doesNothing :: forall ca cem cr. Advice ca cem cr
--  doesNothing = makeExecutionAdvice id
-- :}
--
makeExecutionAdvice ::
  forall ca cem cr.
  -- | The function that tweaks the execution.
  ( forall e m r.
    (cem e m, Monad m, cr r) =>
    DepT e m r ->
    DepT e m r
  ) ->
  Advice ca cem cr
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
-- >>> type FooAdvice = Advice Top (Ensure HasLogger) Top
--
-- Why is it necessary? Two-place @HasX@-style constraints receive the \"fully
-- applied\" type of the record-of-functions. That is: @NilEnv IO@ instead of
-- simply @NilEnv@. This allows them to also work with monomorphic
-- environments (like those in <http://hackage.haskell.org/package/rio RIO>) whose type isn't parameterized by any monad.
--
-- But the @cem@ constraint works with the type constructor of the environment
-- record, of kind @(Type -> Type) -> Type@, and not with the fully applied
-- type of kind @Type@.
--
type Ensure :: (Type -> (Type -> Type) -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
class c (e (DepT e m)) (DepT e m) => Ensure c e m

instance c (e (DepT e m)) (DepT e m) => Ensure c e m

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
--  advisedFoo1 = advise (returnMempty @Top @Top2) foo
--  advisedFoo2 = advise @Top @Top2 returnMempty foo
--  advisedFoo3 = advise (printArgs @Top stdout "args: ") foo
--  advisedFoo4 = advise @_ @_ @Top (printArgs stdout "args: ") foo
-- :}
--
--
advise ::
  forall ca cem cr as e m r advisee.
  (Multicurryable as e m r advisee, All ca as, cem e m, Monad m, cr r) =>
  -- | The advice to apply.
  Advice ca cem cr ->
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
  type EndingInTheBaseMonad as e m r curried :: Type
  multiuncurry :: curried -> NP I as -> DepT e m r
  multicurry :: (NP I as -> DepT e m r) -> curried
  _runFromEnv :: (e (DepT e m) -> curried) -> m (e (DepT e m)) -> EndingInTheBaseMonad as e m r curried

instance Monad m => Multicurryable '[] e m r (DepT e m r) where
  type EndingInTheBaseMonad '[] e m r (DepT e m r) = m r
  multiuncurry action Nil = action
  multicurry f = f Nil
  _runFromEnv extractor eaction = do
    e <- eaction
    runDepT (extractor e) e

instance Multicurryable as e m r curried => Multicurryable (a ': as) e m r (a -> curried) where
  type EndingInTheBaseMonad (a ': as) e m r (a -> curried) = a -> EndingInTheBaseMonad as e m r curried
  multiuncurry f (I a :* as) = multiuncurry @as @e @m @r @curried (f a) as
  multicurry f a = multicurry @as @e @m @r @curried (f . (:*) (I a))
  _runFromEnv extractor eaction a = _runFromEnv @as @e @m @r @curried (\f -> extractor f a) eaction

-- | Run the 'DepT' transformer at the end of a curried function, using an
-- environment obtained from an action in the base monad.
--
-- >>> :{ 
--  foo :: Int -> Int -> Int -> DepT NilEnv IO ()
--  foo _ _ _ = pure ()
-- :}
--
--  >>> runFinalDepT foo (pure NilEnv) 1 2 3 :: IO ()
--
runFinalDepT :: forall as e m r curried . Multicurryable as e m r curried => curried -> m (e (DepT e m)) -> EndingInTheBaseMonad as e m r curried
runFinalDepT extractor = _runFromEnv (const extractor)

runFromEnv :: forall as e m r curried . (Multicurryable as e m r curried, Monad m) => (e (DepT e m) -> curried) -> m (e (DepT e m)) -> EndingInTheBaseMonad as e m r curried
runFromEnv = _runFromEnv

-- |
--    A two-place constraint which requires nothing of the environment and the
--    base monad.
--
--    Useful as the @cem@ type application argument of 'advise' and 'restrictEnv'.
--
--    For similar behavior with the @ar@ and @cr@ type arguments of 'advise' and
--    'restrictEnv', use 'Top' from \"sop-core\".
--
-- >>> type UselessAdvice = Advice Top Top2 Top
--
type Top2 :: ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
class Top2 e m

instance Top2 e m

-- |
--    Combines two two-place constraints on the environment / monad pair.
--
--    For example, an advice which requires both @Ensure HasLogger@ and @Ensure
--    HasRepository@ might use this.
--
--    Useful to build the @cem@ type application argument of 'advise' and
--    'restrictEnv'.
--
--    For similar behavior with the @ar@ and @cr@ type arguments of 'advise' and
--    'restrictEnv', use 'And' from \"sop-core\".
type And2 ::
  (((Type -> Type) -> Type) -> (Type -> Type) -> Constraint) ->
  (((Type -> Type) -> Type) -> (Type -> Type) -> Constraint) ->
  (((Type -> Type) -> Type) -> (Type -> Type) -> Constraint)
class (f e m, g e m) => (f `And2` g) e m

instance (f e m, g e m) => (f `And2` g) e m

infixl 7 `And2`

-- | A class synonym for @(~)@, the type equality constraint. 
--
-- Poly-kinded, so it can be applied both to type constructors (like monads) and to concrete types.
--
-- It this library it will be used partially applied:
--
-- >>> type FooAdvice = Advice Top (MonadConstraint (MustBe IO)) Top
--
-- >>>  type FooAdvice = Advice Top Top2 (MustBe String)
--
type MustBe :: forall k. k -> k -> Constraint 
class x ~ y => MustBe x y
instance x ~ y => MustBe x y

-- |
-- Pins both the environment type constructor and the base monad. Sometimes we
-- don't want to advise functions in some generic environment, but in a
-- concrete environment having access to all the fields, and in a concrete base
-- monad. 
--
-- Useful to build the @cem@ type application argument of 'advise' and
-- 'restricEnv'.
--
-- For similar behavior with the @ar@ and @cr@ type arguments of 'advise'
-- and 'restrictEnv', use 'MustBe'.
--
-- It this library it will be used partially applied:
--
-- >>> type FooAdvice = Advice Top (MustBe2 NilEnv IO) Top
--
type MustBe2 :: ((Type -> Type) -> Type) -> (Type -> Type) -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
class (e' ~ e, m' ~ m) => MustBe2 e' m' e m

instance (e' ~ e, m' ~ m) => MustBe2 e' m' e m

-- |
--    Require a constraint only on the /unapplied/ environment type constructor, which has kind @(Type -> Type) -> Type@.
--
--    Can be used to build @cem@ type application argument of 'advise' and 'restrictEnv'.
--
--    Most of the time this is /not/ what you want. One exception is when
--    pinning the environment with a 'MustBe' equality constraint, while
--    leaving the base monad free:
--
--    >>> type FooAdvice = Advice Top (EnvConstraint (MustBe NilEnv)) Top
--
--    If what you want is to lift a two-parameter @HasX@-style typeclass to @cem@, use 'Ensure' instead.
--
type EnvConstraint :: (((Type -> Type) -> Type) -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
class c e => EnvConstraint c e m

instance c e => EnvConstraint c e m

-- |
--    Require a constraint only on the base monad, for example a base moonad with @MonadIO@.
--
--    Useful to build @cem@ type application argument of 'advise' and 'restrictEnv'.
--
--    >>> type FooAdvice = Advice Top (MonadConstraint MonadIO) Top
--
--    >>> type FooAdvice = Advice Top (MonadConstraint (MonadReader Int)) Top
--
type MonadConstraint :: ((Type -> Type) -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
class c m => MonadConstraint c e m

instance c m => MonadConstraint c e m

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
-- >>> :{
-- returnMempty' :: Advice ca cem (Monoid `And` Show)
-- returnMempty' = restrictResult (Sub Dict) returnMempty
-- :}
--
-- or with a type application to the restriction function:
--
-- >>> :{ 
-- returnMempty'' :: Advice ca cem (Monoid `And` Show)
-- returnMempty'' = restrictResult @(Monoid `And` Show) (Sub Dict) returnMempty
-- :}
--
-- Another example:
--
-- >>> :{
--  type HasLogger :: Type -> (Type -> Type) -> Constraint
--  class HasLogger em m | em -> m where
--    logger :: em -> String -> m ()
--  doLogging :: Advice Show (Ensure HasLogger) cr
--  doLogging = undefined
--  type EnsureLoggerAndWriter :: ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
--  type EnsureLoggerAndWriter = Ensure HasLogger `And2` MonadConstraint MonadIO
--  doLogging':: Advice Show EnsureLoggerAndWriter cr
--  doLogging'= restrictEnv (Sub Dict) doLogging
--  doLogging'' = restrictEnv @EnsureLoggerAndWriter (Sub Dict) doLogging
-- :} 
--
--

-- | Makes the constraint on the arguments more restrictive.
restrictArgs ::
  forall more less cem cr.
  -- | Evidence that one constraint implies the other.
  (forall r. more r :- less r) ->
  -- | Advice with less restrictive constraint on the args.
  Advice less cem cr ->
  -- | Advice with more restrictive constraint on the args.
  Advice more cem cr
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
        forall more less cem cr u.
        (forall r. more r :- less r) ->
        Proxy u ->
        ( forall as e m.
          (All less as, cem e m, Monad m) =>
          NP I as ->
          DepT e m (u, NP I as)
        ) ->
        ( forall e m r.
          (cem e m, Monad m, cr r) =>
          u ->
          DepT e m r ->
          DepT e m r
        ) ->
        Advice more cem cr
      captureExistential evidence' _ tweakArgs' tweakExecution' =
        Advice
          (Proxy @u)
          ( let tweakArgs'' :: forall as e m. (All more as, cem e m, Monad m) => NP I as -> DepT e m (u, NP I as)
                tweakArgs'' = case SOP.mapAll @more @less (translateEvidence @more @less evidence') of
                  f -> case f (SOP.Dict @(All more) @as) of
                    SOP.Dict -> \args -> tweakArgs' @as @e @m args
             in tweakArgs''
          )
          tweakExecution'
   in captureExistential evidence proxy tweakArgs tweakExecution

-- |
--    Makes the constraint on the environment / monad more restrictive.
restrictEnv ::
  forall more ca less cr.
  -- | Evidence that one constraint implies the other.
  (forall e m. more e m :- less e m) ->
  -- | Advice with less restrictive constraint on the environment and base monad.
  Advice ca less cr ->
  -- | Advice with more restrictive constraint on the environment and base monad.
  Advice ca more cr
restrictEnv evidence (Advice proxy tweakArgs tweakExecution) =
  let captureExistential ::
        forall more ca less cr u.
        (forall e m. more e m :- less e m) ->
        Proxy u ->
        ( forall as e m.
          (All ca as, less e m, Monad m) =>
          NP I as ->
          DepT e m (u, NP I as)
        ) ->
        ( forall e m r.
          (less e m, Monad m, cr r) =>
          u ->
          DepT e m r ->
          DepT e m r
        ) ->
        Advice ca more cr
      captureExistential evidence' _ tweakArgs' tweakExecution' =
        Advice
          (Proxy @u)
          ( let tweakArgs'' :: forall as e m. (All ca as, more e m, Monad m) => NP I as -> DepT e m (u, NP I as)
                tweakArgs'' = case evidence' @e @m of Sub Dict -> \args -> tweakArgs' @as @e @m args
             in tweakArgs''
          )
          ( let tweakExecution'' :: forall e m r. (more e m, Monad m, cr r) => u -> DepT e m r -> DepT e m r
                tweakExecution'' = case evidence' @e @m of Sub Dict -> \u action -> tweakExecution' @e @m @r u action
             in tweakExecution''
          )
   in captureExistential evidence proxy tweakArgs tweakExecution

-- |
--    Makes the constraint on the result more restrictive.
restrictResult ::
  forall more ca cem less.
  -- | Evidence that one constraint implies the other.
  (forall r. more r :- less r) ->
  -- | Advice with less restrictive constraint on the result.
  Advice ca cem less ->
  -- | Advice with more restrictive constraint on the result.
  Advice ca cem more
restrictResult evidence (Advice proxy tweakArgs tweakExecution) =
  let captureExistential ::
        forall more ca cem less u.
        (forall r. more r :- less r) ->
        Proxy u ->
        ( forall as e m.
          (All ca as, cem e m, Monad m) =>
          NP I as ->
          DepT e m (u, NP I as)
        ) ->
        ( forall e m r.
          (cem e m, Monad m, less r) =>
          u ->
          DepT e m r ->
          DepT e m r
        ) ->
        Advice ca cem more
      captureExistential evidence' _ tweakArgs' tweakExecution' =
        Advice
          (Proxy @u)
          tweakArgs'
          ( let tweakExecution'' :: forall e m r. (cem e m, Monad m, more r) => u -> DepT e m r -> DepT e m r
                tweakExecution'' = case evidence' @r of Sub Dict -> \u action -> tweakExecution' @e @m @r u action
             in tweakExecution''
          )
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
-- 'Dict' and '(:-)' are GADTs used to capture and transform constraints. Used in the 'restrictArgs', 'restrictEnv' and 'restrictResult' functions.
--


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
--

-- $invocation
-- There functions are helpers for running 'DepT' computations, beyond what 'runDepT' provides.
--
-- They aren't directly related to 'Advice's, but they require some of the same machinery, and that's why they are here.
--
--
