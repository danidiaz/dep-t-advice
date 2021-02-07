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

    -- * Advising and deceiving whole records
    adviseRecord,
    deceiveRecord,

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
import Control.Monad.Trans.Reader (ReaderT (..), withReaderT)
import Data.Kind
import Data.SOP
import Data.SOP.Dict
import Data.SOP.NP
import GHC.Generics qualified as G

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

-- | A generic transformation of 'DepT'-effectful functions with environment
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
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Type ->
  Type
data Advice ca e_ m r where
  Advice ::
    forall u ca e_ m r.
    Proxy u ->
    ( forall as.
      All ca as =>
      NP I as ->
      DepT e_ m (u, NP I as)
    ) ->
    ( u ->
      DepT e_ m r ->
      DepT e_ m r
    ) ->
    Advice ca e_ m r

-- |
--    'Advice's compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'DepT' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Monad m => Semigroup (Advice ca e_ m r) where
  Advice outer tweakArgsOuter tweakExecutionOuter <> Advice inner tweakArgsInner tweakExecutionInner =
    let captureExistentials ::
          forall ca e_ r outer inner.
          Proxy outer ->
          ( forall as.
            All ca as =>
            NP I as ->
            DepT e_ m (outer, NP I as)
          ) ->
          ( outer ->
            DepT e_ m r ->
            DepT e_ m r
          ) ->
          Proxy inner ->
          ( forall as.
            All ca as =>
            NP I as ->
            DepT e_ m (inner, NP I as)
          ) ->
          ( inner ->
            DepT e_ m r ->
            DepT e_ m r
          ) ->
          Advice ca e_ m r
        captureExistentials _ tweakArgsOuter' tweakExecutionOuter' _ tweakArgsInner' tweakExecutionInner' =
          Advice
            (Proxy @(Pair outer inner))
            ( let tweakArgs ::
                    forall as.
                    All ca as =>
                    NP I as ->
                    DepT e_ m (Pair outer inner, NP I as)
                  tweakArgs args =
                    do
                      (uOuter, argsOuter) <- tweakArgsOuter' @as args
                      (uInner, argsInner) <- tweakArgsInner' @as argsOuter
                      pure (Pair uOuter uInner, argsInner)
               in tweakArgs
            )
            ( let tweakExecution ::
                    Pair outer inner ->
                    DepT e_ m r ->
                    DepT e_ m r
                  tweakExecution =
                    ( \(Pair uOuter uInner) action ->
                        tweakExecutionOuter' uOuter (tweakExecutionInner' uInner action)
                    )
               in tweakExecution
            )
     in captureExistentials @ca @e_ outer tweakArgsOuter tweakExecutionOuter inner tweakArgsInner tweakExecutionInner

instance Monad m => Monoid (Advice ca e_ m r) where
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
  forall u ca e_ m r.
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    DepT e_ m (u, NP I as)
  ) ->
  -- | The function that tweaks the execution.
  ( u ->
    DepT e_ m r ->
    DepT e_ m r
  ) ->
  Advice ca e_ m r
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
  forall ca e_ m r.
  Monad m =>
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    DepT e_ m (NP I as)
  ) ->
  Advice ca e_ m r
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
  forall ca e_ m r.
  Applicative m =>
  -- | The function that tweaks the execution.
  ( DepT e_ m r ->
    DepT e_ m r
  ) ->
  Advice ca e_ m r
makeExecutionAdvice tweakExecution = makeAdvice @() (\args -> pure (pure args)) (\() action -> tweakExecution action)

data Pair a b = Pair !a !b

-- |
-- 'Ensure' is a helper for lifting typeclass definitions of the form:
--
-- >>> :{
--  type HasLogger :: (Type -> Type) -> Type -> Constraint
--  class HasLogger d e | e -> d where
--    logger :: e -> String -> d ()
-- :}
--
-- To work as a constraints on the @e_@ and @m@ parameters of an 'Advice', like this:
--
-- >>> :{
--  requiresLogger :: forall e_ m r. (Ensure HasLogger e_ m, Monad m) => Advice Show e_ m r
--  requiresLogger = mempty
--  :}
--
-- Why is it necessary? Two-place @HasX@-style constraints receive the \"fully
-- applied\" type of the record-of-functions. That is: @NilEnv IO@ instead of
-- simply @NilEnv@. This allows them to also work with monomorphic environments
-- (like those in <http://hackage.haskell.org/package/rio RIO>) whose type
-- isn't parameterized by any monad.
--
-- But the @e_@ type parameter of 'Advice' has kind @(Type -> Type) -> Type@.
-- That is: @NilEnv@ alone.
--
-- Furthermore, 'Advices' require @HasX@-style constraints to be placed on the
-- @DepT@ transformer, not directly on the base monad @m@. @Ensure@ takes care
-- of that as well.
type Ensure :: ((Type -> Type) -> Type -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint

type Ensure c e_ m = c (DepT e_ m) (e_ (DepT e_ m))

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
  forall ca e_ m r as advisee.
  (Multicurryable as e_ m r advisee, All ca as, Monad m) =>
  -- | The advice to apply.
  Advice ca e_ m r ->
  -- | A function to be adviced.
  advisee ->
  advisee
advise (Advice _ tweakArgs tweakExecution) advisee = do
  let uncurried = multiuncurry @as @e_ @m @r advisee
      uncurried' args = do
        (u, args') <- tweakArgs args
        tweakExecution u (uncurried args')
   in multicurry @as @e_ @m @r uncurried'

type Multicurryable ::
  [Type] ->
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Type ->
  Type ->
  Constraint
class Multicurryable as e_ m r curried | curried -> as e_ m r where
  type DownToBaseMonad as e_ m r curried :: Type
  multiuncurry :: curried -> NP I as -> DepT e_ m r
  multicurry :: (NP I as -> DepT e_ m r) -> curried
  _runFromEnv :: m (e_ (DepT e_ m)) -> (e_ (DepT e_ m) -> curried) -> DownToBaseMonad as e_ m r curried

instance Monad m => Multicurryable '[] e_ m r (DepT e_ m r) where
  type DownToBaseMonad '[] e_ m r (DepT e_ m r) = m r
  multiuncurry action Nil = action
  multicurry f = f Nil
  _runFromEnv producer extractor = do
    e <- producer
    runDepT (extractor e) e

instance Multicurryable as e_ m r curried => Multicurryable (a ': as) e_ m r (a -> curried) where
  type DownToBaseMonad (a ': as) e_ m r (a -> curried) = a -> DownToBaseMonad as e_ m r curried
  multiuncurry f (I a :* as) = multiuncurry @as @e_ @m @r @curried (f a) as
  multicurry f a = multicurry @as @e_ @m @r @curried (f . (:*) (I a))
  _runFromEnv producer extractor a = _runFromEnv @as @e_ @m @r @curried producer (\f -> extractor f a)

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
  forall as e_ m r curried.
  Multicurryable as e_ m r curried =>
  -- | action that gets hold of the environment
  m (e_ (DepT e_ m)) ->
  -- | function to invoke with effects in 'DepT'
  curried ->
  -- | a new function with effects in the base monad
  DownToBaseMonad as e_ m r curried
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
  forall as e_ m r curried.
  Multicurryable as e_ m r curried =>
  -- | action that gets hold of the environment
  m (e_ (DepT e_ m)) ->
  -- | gets a function from the environment with effects in 'DepT'
  (e_ (DepT e_ m) -> curried) ->
  -- | a new function with effects in the base monad
  DownToBaseMonad as e_ m r curried
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
--  stricterPrintArgs :: forall e_ m r. MonadIO m => Advice (Show `And` Eq `And` Ord) e_ m r
--  stricterPrintArgs = restrictArgs (\Dict -> Dict) (printArgs stdout "foo")
-- :}
--
--    or with a type application to 'restrictArgs':
--
-- >>> stricterPrintArgs = restrictArgs @(Show `And` Eq `And` Ord) (\Dict -> Dict) (printArgs stdout "foo")

-- | Makes the constraint on the arguments more restrictive.
restrictArgs ::
  forall more less e_ m r.
  -- | Evidence that one constraint implies the other. Every @x@ that has a @more@ instance also has a @less@ instance.
  (forall x. Dict more x -> Dict less x) ->
  -- | Advice with less restrictive constraint on the args.
  Advice less e_ m r ->
  -- | Advice with more restrictive constraint on the args.
  Advice more e_ m r
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
        forall more less e_ m r u.
        (forall x. Dict more x -> Dict less x) ->
        Proxy u ->
        ( forall as.
          All less as =>
          NP I as ->
          DepT e_ m (u, NP I as)
        ) ->
        ( u ->
          DepT e_ m r ->
          DepT e_ m r
        ) ->
        Advice more e_ m r
      captureExistential evidence' _ tweakArgs' tweakExecution' =
        Advice
          (Proxy @u)
          ( let tweakArgs'' :: forall as. All more as => NP I as -> DepT e_ m (u, NP I as)
                tweakArgs'' = case Data.SOP.Dict.mapAll @more @less evidence' of
                  f -> case f (Dict @(All more) @as) of
                    Dict -> \args -> tweakArgs' @as args
             in tweakArgs''
          )
          tweakExecution'
   in captureExistential evidence proxy tweakArgs tweakExecution

--
type Gullible ::
  [Type] ->
  Type ->
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Type ->
  Type ->
  Constraint
class Multicurryable as e_ m r curried => Gullible as e e_ m r curried where
  type NewtypedEnv as e e_ m r curried :: Type
  _deceive :: (e_ (DepT e_ m) -> e) -> NewtypedEnv as e e_ m r curried -> curried

instance Monad m => Gullible '[] e e_ m r (DepT e_ m r) where
  type NewtypedEnv '[] e e_ m r (DepT e_ m r) = ReaderT e m r
  _deceive f action = DepT (withReaderT f action)

instance Gullible as e e_ m r curried => Gullible (a ': as) e e_ m r (a -> curried) where
  type NewtypedEnv (a ': as) e e_ m r (a -> curried) = a -> NewtypedEnv as e e_ m r curried
  _deceive f g a = deceive @as @e @e_ @m @r f (g a)

-- | Makes a function see a newtyped version of the environment record, a version that might have different @HasX@ instances.
--
-- The \"deception\" doesn't affect the dependencies used by the function, only the function itself.
--
-- For example, consider the following setup which features both a \"deceviced\"
-- and an \"undeceived\" version of a controller function:
--
-- >>> :{
--  type HasLogger :: (Type -> Type) -> Type -> Constraint
--  class HasLogger d e | e -> d where
--    logger :: e -> String -> d ()
--  type HasIntermediate :: (Type -> Type) -> Type -> Constraint
--  class HasIntermediate d e | e -> d where
--    intermediate :: e -> String -> d ()
--  type Env :: (Type -> Type) -> Type
--  data Env m = Env
--    { _logger1 :: String -> m (),
--      _logger2 :: String -> m (),
--      _intermediate :: String -> m (),
--      _controllerA :: Int -> m (),
--      _controllerB :: Int -> m ()
--    }
--  instance HasLogger m (Env m) where
--    logger = _logger1
--  instance HasIntermediate m (Env m) where
--    intermediate = _intermediate
--  newtype Switcheroo m = Switcheroo (Env m)
--      deriving newtype (HasIntermediate m)
--  instance HasLogger m (Switcheroo m) where
--    logger (Switcheroo e) = _logger2 e
--  env :: Env (DepT Env (Writer [String]))
--  env =
--    let mkController :: forall d e m. MonadDep [HasLogger, HasIntermediate] d e m => Int -> m ()
--        mkController _ = do e <- ask; liftD $ logger e "foo" ; liftD $ intermediate e "foo"
--        mkIntermediate :: forall d e m. MonadDep '[HasLogger] d e m => String -> m ()
--        mkIntermediate _ = do e <- ask ; liftD $ logger e "foo"
--     in Env
--        {
--          _logger1 =
--             \_ -> tell ["logger 1"],
--          _logger2 =
--             \_ -> tell ["logger 2"],
--          _intermediate =
--             mkIntermediate,
--          _controllerA =
--             mkController,
--          _controllerB =
--             deceive Switcheroo $
--             mkController
--        }
-- :}
--
-- If we run @_controllerA@ the ouput is:
--
-- >>> execWriter $ runFromEnv (pure env) _controllerA 7
-- ["logger 1","logger 1"]
--
-- But if we run the \"deceived\" @_controllerB@, we see that the function and its @_intermediate@ dependency use different loggers:
--
-- >>> execWriter $ runFromEnv (pure env) _controllerB 7
-- ["logger 2","logger 1"]
--
-- Note that the function that is \"deceived\" must be polymorphic over
-- 'Control.Monad.Dep.MonadDep'. Passing a function whose effect monad has
-- already \"collapsed\" into 'DepT' won't work. Therefore, 'deceive' must be applied before any 'Advice'.
deceive ::
  forall as e e_ m r curried.
  Gullible as e e_ m r curried =>
  -- | The newtype constructor that masks the \"true\" environment.
  (e_ (DepT e_ m) -> e) ->
  -- | A function to be deceived. It must be polymorphic over 'Control.Monad.Dep.MonadDep'.
  NewtypedEnv as e e_ m r curried ->
  -- | The deceived function, that has effects in 'DepT'.
  curried
deceive = _deceive

-- deceving *all* fields of a record
--
--
type GullibleRecord :: Type -> ((Type -> Type) -> Type) -> (Type -> Type) -> ((Type -> Type) -> Type) -> Constraint
class GullibleRecord e e_ m gullible where
  _deceiveRecord :: (e_ (DepT e_ m) -> e) -> gullible (ReaderT e m) -> gullible (DepT e_ m)

-- https://gitlab.haskell.org/ghc/ghc/-/issues/13952
type GullibleProduct :: Type -> ((Type -> Type) -> Type) -> (Type -> Type) -> (k -> Type) -> (k -> Type) -> Constraint
class GullibleProduct e e_ m gullible_ deceived_ | e e_ m deceived_ -> gullible_ where
  _deceiveProduct :: (e_ (DepT e_ m) -> e) -> gullible_ k -> deceived_ k

instance
  ( GullibleProduct e e_ m gullible_left deceived_left,
    GullibleProduct e e_ m gullible_right deceived_right
  ) =>
  GullibleProduct e e_ m (gullible_left G.:*: gullible_right) (deceived_left G.:*: deceived_right)
  where
  _deceiveProduct f (gullible_left G.:*: gullible_right) = _deceiveProduct @_ @e @e_ @m f gullible_left G.:*: _deceiveProduct @_ @e @e_ @m f gullible_right

data RecordComponent
  = Terminal
  | Recurse

type DiscriminateGullibleComponent :: Type -> RecordComponent
type family DiscriminateGullibleComponent c where
  DiscriminateGullibleComponent (a -> b) = Terminal
  DiscriminateGullibleComponent (ReaderT e m x) = Terminal
  DiscriminateGullibleComponent _ = Recurse

type GullibleComponent :: RecordComponent -> Type -> ((Type -> Type) -> Type) -> (Type -> Type) -> Type -> Type -> Constraint
class GullibleComponent component_type e e_ m gullible deceived | e e_ m deceived -> gullible where
  _deceiveComponent :: (e_ (DepT e_ m) -> e) -> gullible -> deceived

instance
  (Gullible as e e_ m r deceived, NewtypedEnv as e e_ m r deceived ~ gullible) =>
  GullibleComponent Terminal e e_ m gullible deceived
  where
  _deceiveComponent f gullible = deceive @as @e @_ @m @r f gullible

instance
  GullibleRecord e e_ m gullible =>
  GullibleComponent Recurse e e_ m (gullible (ReaderT e m)) (gullible (DepT e_ m))
  where
  _deceiveComponent f gullible = _deceiveRecord @e @e_ @m f gullible

instance
  GullibleComponent (DiscriminateGullibleComponent gullible) e e_ m gullible deceived =>
  GullibleProduct e e_ m (G.S1 x (G.Rec0 gullible)) (G.S1 x (G.Rec0 deceived))
  where
  _deceiveProduct f (G.M1 (G.K1 gullible)) = G.M1 (G.K1 (_deceiveComponent @(DiscriminateGullibleComponent gullible) @e @e_ @m f gullible))

instance
  ( G.Generic (gullible (ReaderT e m)),
    G.Generic (gullible (DepT e_ m)),
    G.Rep (gullible (ReaderT e m)) ~ G.D1 x (G.C1 y gullible_),
    G.Rep (gullible (DepT e_ m)) ~ G.D1 x (G.C1 y deceived_),
    GullibleProduct e e_ m gullible_ deceived_
  ) =>
  GullibleRecord e e_ m gullible
  where
  _deceiveRecord f gullible =
    let G.M1 (G.M1 gullible_) = G.from gullible
        deceived_ = _deceiveProduct @_ @e @e_ @m f gullible_
     in G.to (G.M1 (G.M1 deceived_))

deceiveRecord ::
  forall e e_ m gullible.
  GullibleRecord e e_ m gullible =>
  -- | The newtype constructor that masks the \"true\" environment.
  (e_ (DepT e_ m) -> e) ->
  -- | The parameterized record to "deceive" recursively.
  gullible (ReaderT e m) ->
  -- | The deceived record.
  gullible (DepT e_ m)
deceiveRecord = _deceiveRecord @e @e_ @m @gullible

-- advising *all* fields of a record
--
--
type AdvisedRecord :: (Type -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> (Type -> Constraint) -> ((Type -> Type) -> Type) -> Constraint
class AdvisedRecord ca e_ m cr advised where
  _adviseRecord :: (forall r. cr r => Advice ca e_ m r) -> advised (DepT e_ m) -> advised (DepT e_ m)

type AdvisedProduct :: (Type -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> (Type -> Constraint) -> (k -> Type) -> Constraint
class AdvisedProduct ca e_ m cr advised_ where
  _adviseProduct :: (forall r. cr r => Advice ca e_ m r) -> advised_ k -> advised_ k

instance
  ( G.Generic (advised (DepT e_ m)),
    G.Rep (advised (DepT e_ m)) ~ G.D1 x (G.C1 y advised_),
    AdvisedProduct ca e_ m cr advised_
  ) =>
  AdvisedRecord ca e_ m cr advised
  where
  _adviseRecord advice unadvised =
    let G.M1 (G.M1 unadvised_) = G.from unadvised
        advised_ = _adviseProduct @_ @ca @e_ @m @cr advice unadvised_
     in G.to (G.M1 (G.M1 advised_))

instance
  ( AdvisedProduct ca e_ m cr advised_left,
    AdvisedProduct ca e_ m cr advised_right
  ) =>
  AdvisedProduct ca e_ m cr (advised_left G.:*: advised_right)
  where
  _adviseProduct f (unadvised_left G.:*: unadvised_right) = _adviseProduct @_ @ca @e_ @m @cr f unadvised_left G.:*: _adviseProduct @_ @ca @e_ @m @cr f unadvised_right

type DiscriminateAdvisedComponent :: Type -> RecordComponent
type family DiscriminateAdvisedComponent c where
  DiscriminateAdvisedComponent (a -> b) = Terminal
  DiscriminateAdvisedComponent (DepT e_ m x) = Terminal
  DiscriminateAdvisedComponent _ = Recurse

type AdvisedComponent :: RecordComponent -> (Type -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> (Type -> Constraint) -> Type -> Constraint
class AdvisedComponent component_type ca e_ m cr advised where
  _adviseComponent :: (forall r. cr r => Advice ca e_ m r) -> advised -> advised

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca e_ m cr advised =>
  AdvisedProduct ca e_ m cr (G.S1 x (G.Rec0 advised))
  where
  _adviseProduct f (G.M1 (G.K1 advised)) = G.M1 (G.K1 (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @e_ @m @cr f advised))

instance
  AdvisedRecord ca e_ m cr advisable =>
  AdvisedComponent Recurse ca e_ m cr (advisable (DepT e_ m))
  where
  _adviseComponent f advised = _adviseRecord @ca @e_ @m @cr f advised

instance
  (Multicurryable as e_ m r advised, All ca as, cr r, Monad m) =>
  AdvisedComponent Terminal ca e_ m cr advised
  where
  _adviseComponent f advised = advise @ca @e_ @m f advised

adviseRecord :: forall ca cr e_ m advised. AdvisedRecord ca e_ m cr advised => 
    -- | The advice to apply
    (forall r. cr r => Advice ca e_ m r) -> 
    -- | The record to advise
    advised (DepT e_ m) -> 
    -- | The advised record
    advised (DepT e_ m)
adviseRecord = _adviseRecord @ca @e_ @m @cr

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
