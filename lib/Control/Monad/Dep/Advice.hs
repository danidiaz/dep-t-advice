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
-- And they can be combined using @Advice@'s 'Monoid' instance before being
-- applied:
--
-- >>> advise (printArgs stdout "foo2" <> returnMempty) foo2 'd' False `runDepT` NilEnv
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 0}
--
-- Although sometimes composition might require harmonizing the constraints
-- each 'Advice' places on the arguments, if they differ.
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

    -- * Making functions see a different environment
    deceive,

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

import Control.Monad.Dep
import Control.Monad.Trans.Reader
import Data.Kind
import Data.SOP
import Data.SOP.Dict
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
-- >>> :set -XFlexibleContexts
-- >>> import Control.Monad
-- >>> import Control.Monad.Dep
-- >>> import Control.Monad.Dep.Advice
-- >>> import Control.Monad.Dep.Advice.Basic (printArgs,returnMempty)
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef

-- | A generic transformation of 'DepT'-effectful functions with environment
-- @e@ of kind @(Type -> Type) -> Type@, base monad @m@ and return type @r@,
-- provided the functions satisfy certain constraint @ca@ of kind @Type ->
-- Constraint@ on all of their arguments.
--
-- Note that the type constructor for the environment @e@ is given unapplied.
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
    ( u ->
      DepT e m r ->
      DepT e m r
    ) ->
    Advice ca e m r

-- |
--    'Advice's compose \"sequentially\" when tweaking the arguments, and
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
          ( outer ->
            DepT e m r ->
            DepT e m r
          ) ->
          Proxy inner ->
          ( forall as.
            All ca as =>
            NP I as ->
            DepT e m (inner, NP I as)
          ) ->
          ( inner ->
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
--    __/TYPE APPLICATION REQUIRED!/__ When invoking 'makeAdvice', you must always give the
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
  ( u ->
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
  ( DepT e m r ->
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
-- To work as a constraints on the @e@ and @m@ parameters of an 'Advice', like this:
--
-- >>> :{
--  requiresLogger :: forall e m r. (Ensure HasLogger e m, Monad m) => Advice Show e m r
--  requiresLogger = mempty
--  :}
--
-- Why is it necessary? Two-place @HasX@-style constraints receive the \"fully
-- applied\" type of the record-of-functions. That is: @NilEnv IO@ instead of
-- simply @NilEnv@. This allows them to also work with monomorphic environments
-- (like those in <http://hackage.haskell.org/package/rio RIO>) whose type
-- isn't parameterized by any monad.
--
-- But the @e@ type parameter of 'Advice' has kind @(Type -> Type) -> Type@.
-- That is: @NilEnv@ alone.
--
-- Furthermore, 'Advices' require @HasX@-style constraints to be placed on the
-- @DepT@ transformer, not directly on the base monad @m@. @Ensure@ takes care
-- of that as well.
type Ensure :: (Type -> (Type -> Type) -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint

type Ensure c e m = c (e (DepT e m)) (DepT e m)

-- | Apply an 'Advice' to some compatible function. The function must have its
-- effects in 'DepT', and all of its arguments must satisfy the @ca@ constraint.
--
-- >>> :{
--  foo :: Int -> DepT NilEnv IO String
--  foo _ = pure "foo"
--  advisedFoo = advise (printArgs stdout "Foo args: ") foo
-- :}
--
-- __/TYPE APPLICATION REQUIRED!/__ If the @ca@ constraint of the 'Advice' remains polymorphic,
-- it must be supplied by means of a type application:
--
-- >>> :{
--  bar :: Int -> DepT NilEnv IO String
--  bar _ = pure "bar"
--  advisedBar1 = advise (returnMempty @Top) bar
--  advisedBar2 = advise @Top returnMempty bar
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
--  stricterPrintArgs :: forall e m r. MonadIO m => Advice (Show `And` Eq `And` Ord) NilEnv m r
--  stricterPrintArgs = restrictArgs (\Dict -> Dict) (printArgs stdout "foo")
-- :}
--
--    or with a type application to 'restrictArgs':
--
-- >>> stricterPrintArgs = restrictArgs @(Show `And` Eq `And` Ord) (\Dict -> Dict) (printArgs stdout "foo")

-- | Makes the constraint on the arguments more restrictive.
restrictArgs ::
  forall more less e m r.
  -- | Evidence that one constraint implies the other. Every @x@ that has a @more@ instance also has a @less@ instance.
  (forall x. Dict more x -> Dict less x) ->
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
        (forall x. Dict more x -> Dict less x) ->
        Proxy u ->
        ( forall as.
          All less as =>
          NP I as ->
          DepT e m (u, NP I as)
        ) ->
        ( u ->
          DepT e m r ->
          DepT e m r
        ) ->
        Advice more e m r
      captureExistential evidence' _ tweakArgs' tweakExecution' =
        Advice
          (Proxy @u)
          ( let tweakArgs'' :: forall as. All more as => NP I as -> DepT e m (u, NP I as)
                tweakArgs'' = case Data.SOP.Dict.mapAll @more @less evidence' of
                  f -> case f (Dict @(All more) @as) of
                    Dict -> \args -> tweakArgs' @as args
             in tweakArgs''
          )
          tweakExecution'
   in captureExistential evidence proxy tweakArgs tweakExecution

--
class Multicurryable as e m r curried => Deceivable as newtyped e m r curried where
  type Deceived as newtyped e m r curried :: Type
  _deceive :: (e (DepT e m) -> newtyped) -> Deceived as newtyped e m r curried -> curried

instance Monad m => Deceivable '[] newtyped e m r (DepT e m r) where
  type Deceived '[] newtyped e m r (DepT e m r) = ReaderT newtyped m r
  _deceive f action = DepT (withReaderT f action)

instance Deceivable as newtyped e m r curried => Deceivable (a ': as) newtyped e m r (a -> curried) where
  type Deceived (a ': as) newtyped e m r (a -> curried) = a -> Deceived as newtyped e m r curried
  _deceive f g a = deceive @as @newtyped @e @m @r f (g a)

deceive ::
  forall as newtyped e m r curried.
  Deceivable as newtyped e m r curried =>
  -- | The newtype constructor that masks the \"true\" environment.
  (e (DepT e m) -> newtyped) ->
  -- | A function to be deceived. It should be polymorphic over 'Control.Monad.Dep.MonadDep'.
  Deceived as newtyped e m r curried ->
  -- | The deceived function, that has effects in 'DepT'.
  curried
deceive = _deceive

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
-- These functions are helpers for running 'DepT' computations, beyond what 'runDepT' provides.
--
-- They aren't directly related to 'Advice's, but they require some of the same machinery, and that's why they are here.
