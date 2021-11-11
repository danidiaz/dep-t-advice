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

-- |
--    This module provides the 'Advice' datatype, along for functions for creating,
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
-- >>> advise (fromSimple \_ -> printArgs stdout "foo0") foo0 `runDepT` NilEnv
-- foo0:
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- And for functions of one or more arguments, provided they end on a @DepT@-action:
--
-- >>> advise (fromSimple \_ -> printArgs stdout "foo1") foo1 False `runDepT` NilEnv
-- foo1: False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- >>> advise (fromSimple \_ -> printArgs stdout "foo2") foo2 'd' False `runDepT` NilEnv
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- 'Advice's can also tweak the result value of functions:
--
-- >>> advise (fromSimple \_ -> returnMempty @Top) foo2 'd' False `runDepT` NilEnv
-- Sum {getSum = 0}
--
-- And they can be combined using @Advice@'s 'Monoid' instance before being
-- applied:
--
-- >>> advise (fromSimple \_ -> printArgs stdout "foo2" <> returnMempty) foo2 'd' False `runDepT` NilEnv
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
    runFromDep,
    -- askFinalDepT,
    -- * Making functions see a different environment
    deceive,

    -- * Advising and deceiving entire records
    -- $records
    adviseRecord,
    deceiveRecord,
    -- * Plugging Has-based constructors
    component,
    --distributeDepT,

    -- * Interfacing with "simple" advices
    toSimple,
    fromSimple,

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
import Control.Monad.Dep.Has
import Control.Monad.Dep.Env
import Control.Monad.Trans.Reader (ReaderT (..), withReaderT)
import Data.Functor.Identity
import Data.Kind
import Data.List.NonEmpty qualified as N
import Data.SOP
import Data.SOP.Dict
import Data.SOP.NP
import Data.Typeable
import GHC.Generics qualified as G
import GHC.TypeLits
import Data.Coerce
import Data.Bifunctor (first)
import Control.Monad.Dep.SimpleAdvice.Internal qualified as SA

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
    forall ca e_ m r.
    ( forall as.
      All ca as =>
      NP I as ->
      DepT e_ m (DepT e_ m r -> DepT e_ m r, NP I as)
    ) ->
    Advice ca e_ m r

-- |
--    'Advice's compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'DepT' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Monad m => Semigroup (Advice ca e_ m r) where
  Advice outer <> Advice inner = Advice \args -> do
    (tweakOuter, argsOuter) <- outer args
    (tweakInner, argsInner) <- inner argsOuter
    pure (tweakOuter . tweakInner, argsInner)

instance Monad m => Monoid (Advice ca e_ m r) where
  mappend = (<>)
  mempty = Advice \args -> pure (id, args)

-- |
--    The most general (and complex) way of constructing 'Advice's.
--
--    An 'Advice' is a function that transforms other functions in an 
--    arity-polymorphic way. It receives the arguments of the advised
--    function packed into an n-ary product 'NP', performs some 
--    effects based on them, and returns a potentially modified version of the 
--    arguments, along with a function for tweaking the execution of the
--    advised function.
--
-- >>> :{
--  doesNothing :: forall ca e_ m r. Monad m => Advice ca e_ m r
--  doesNothing = makeAdvice (\args -> pure (id,  args)) 
-- :}
--
--
makeAdvice ::
  forall ca e_ m r.
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    DepT e_ m (DepT e_ m r -> DepT e_ m r, NP I as)
  ) ->
  Advice ca e_ m r
makeAdvice = Advice

-- |
--    Create an advice which only tweaks and/or analyzes the function arguments.
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
  makeAdvice $ \args -> do
    args' <- tweakArgs args
    pure (id, args')

-- |
--    Create an advice which only tweaks the execution of the final monadic action.
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
makeExecutionAdvice tweakExecution = makeAdvice \args -> pure (tweakExecution, args)

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
--  advisedFoo = advise (fromSimple \_ -> printArgs stdout "Foo args: ") foo
-- :}
--
-- __/TYPE APPLICATION REQUIRED!/__ If the @ca@ constraint of the 'Advice' remains polymorphic,
-- it must be supplied by means of a type application:
--
-- >>> :{
--  bar :: Int -> DepT NilEnv IO String
--  bar _ = pure "bar"
--  advisedBar1 = advise (fromSimple \_ -> returnMempty @Top) bar
--  advisedBar2 = advise @Top (fromSimple \_ -> returnMempty) bar
-- :}
advise ::
  forall ca e_ m r as advisee.
  (Multicurryable as e_ m r advisee, All ca as, Monad m) =>
  -- | The advice to apply.
  Advice ca e_ m r ->
  -- | A function to be adviced.
  advisee ->
  advisee
advise (Advice f) advisee = do
  let uncurried = multiuncurry @as @e_ @m @r advisee
      uncurried' args = do
        (tweakExecution, args') <- f args
        tweakExecution (uncurried args')
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
  _askFinalDepT :: (e_ (DepT e_ m) -> m curried) -> curried

instance Monad m => Multicurryable '[] e_ m r (DepT e_ m r) where
  type DownToBaseMonad '[] e_ m r (DepT e_ m r) = m r
  multiuncurry action Nil = action
  multicurry f = f Nil
  _runFromEnv producer extractor = do
    e <- producer
    runDepT (extractor e) e
  _askFinalDepT f = do
    env <- ask
    r <- lift (f env)
    r

instance (Functor m, Multicurryable as e_ m r curried) => Multicurryable (a ': as) e_ m r (a -> curried) where
  type DownToBaseMonad (a ': as) e_ m r (a -> curried) = a -> DownToBaseMonad as e_ m r curried
  multiuncurry f (I a :* as) = multiuncurry @as @e_ @m @r @curried (f a) as
  multicurry f a = multicurry @as @e_ @m @r @curried (f . (:*) (I a))
  _runFromEnv producer extractor a = _runFromEnv @as @e_ @m @r @curried producer (\f -> extractor f a)
  _askFinalDepT f = 
    let switcheroo action a = fmap ($ a) action
     in _askFinalDepT @as @e_ @m @r . flip (fmap switcheroo f)

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

askFinalDepT ::
  forall as e_ m r curried. 
  Multicurryable as e_ m r curried =>
  (e_ (DepT e_ m) -> m curried) -> curried
askFinalDepT = _askFinalDepT @as @e_ @m @r

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
--      modifyIORef envRef (\e -> e { _foo = advise @Top (fromSimple \_ -> returnMempty) (_foo e) })
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

-- | Like 'runFromEnv', but the function to run is extracted from a dependency
-- @dep@ which is found using 'Has'. The selector should be concrete enough to
-- identify @dep@ in the environment.
runFromDep ::
  forall dep as e_ m r curried.
  (Multicurryable as e_ m r curried, Has dep (DepT e_ m) (e_ (DepT e_ m))) =>
  -- | action that gets hold of the environment
  m (e_ (DepT e_ m)) ->
  -- | selector that gets a function from a dependency found using 'Has'
  (dep (DepT e_ m) -> curried) ->
  -- | a new function with effects in the base monad
  DownToBaseMonad as e_ m r curried
runFromDep envAction member = _runFromEnv envAction (member . dep)

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
--  stricterPrintArgs = restrictArgs (\Dict -> Dict) (fromSimple \_ -> printArgs stdout "foo")
-- :}
--
--    or with a type application to 'restrictArgs':
--
-- >>> stricterPrintArgs = restrictArgs @(Show `And` Eq `And` Ord) (\Dict -> Dict) (fromSimple \_ -> printArgs stdout "foo")

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
restrictArgs evidence (Advice advice) = Advice \args ->
    let advice' :: forall as. All more as => NP I as -> DepT e_ m (DepT e_ m r -> DepT e_ m r, NP I as)
        advice' args' =
            case Data.SOP.Dict.mapAll @more @less evidence of
               f -> case f (Dict @(All more) @as) of
                        Dict -> advice args'
     in advice' args

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

instance (Functor m, Gullible as e e_ m r curried) => Gullible (a ': as) e e_ m r (a -> curried) where
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
  | IWrapped
  | Recurse

type DiscriminateGullibleComponent :: Type -> RecordComponent
type family DiscriminateGullibleComponent c where
  DiscriminateGullibleComponent (a -> b) = Terminal
  DiscriminateGullibleComponent (ReaderT e m x) = Terminal
  DiscriminateGullibleComponent (Identity _) = IWrapped
  DiscriminateGullibleComponent (I _) = IWrapped
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
  GullibleComponent (DiscriminateGullibleComponent gullible) e e_ m gullible deceived =>
  GullibleComponent IWrapped e e_ m (Identity gullible) (Identity deceived)
  where
  _deceiveComponent f (Identity gullible) = Identity (_deceiveComponent @(DiscriminateGullibleComponent gullible) @e @e_ @m f gullible)

instance
  GullibleComponent (DiscriminateGullibleComponent gullible) e e_ m gullible deceived =>
  GullibleComponent IWrapped e e_ m (I gullible) (I deceived)
  where
  _deceiveComponent f (I gullible) = I (_deceiveComponent @(DiscriminateGullibleComponent gullible) @e @e_ @m f gullible)

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

-- | Makes an entire record-of-functions see a different version of the global environment record, a version that might have different @HasX@ instances.
--
-- 'deceiveRecord' must be applied before 'adviseRecord'.
deceiveRecord ::
  forall e e_ m gullible.
  GullibleRecord e e_ m gullible =>
  -- | The newtype constructor that masks the \"true\" environment.
  (e_ (DepT e_ m) -> e) ->
  -- | The record to deceive recursively. The monad parameter must be left polymorphic over @MonadDep@, so that it can unify with `ReaderT`.
  gullible (ReaderT e m) ->
  -- | The deceived record.
  gullible (DepT e_ m)
deceiveRecord = _deceiveRecord @e @e_ @m @gullible


-- | Given a constructor that returns a record-of-functions with effects in 'DepT',
-- produce a record in which the member functions 'ask' for the environment themselves.
--
-- You must have a sufficiently polymorphic constructor—both in the monad and
-- in the environment—to invoke this function.
--
-- 'component' lets you plug simple component constructors 
-- into a 'DepT'-based environment.
--
-- Compare with 'Control.Monad.Dep.Env.constructor' from "Control.Monad.Dep.Env", which 
-- is intended to be used with 'Control.Monad.Dep.Env.fixEnv'-based environments.
component 
    :: forall e_ m record . (Applicative m, DistributiveRecord e_ m record) => 
    -- | constructor which takes the environment as a positional parameter.
    (e_ (DepT e_ m) -> record (DepT e_ m)) ->
    -- | component whose methods get the environment by 'ask'ing.
    record (DepT e_ m)
component f = _distribute @e_ @m (pure . f)



type DistributiveRecord :: ((Type -> Type) -> Type) -> (Type -> Type) -> ((Type -> Type) -> Type) -> Constraint
class DistributiveRecord e_ m record where
    _distribute :: (e_ (DepT e_ m) -> m (record (DepT e_ m))) -> record (DepT e_ m)

type DistributiveProduct :: ((Type -> Type) -> Type) -> (Type -> Type) -> (k -> Type) -> Constraint
class DistributiveProduct e_ m product where
    _distributeProduct :: (e_ (DepT e_ m) -> m (product k)) -> product k

instance
  ( G.Generic (advised (DepT e_ m)),
    G.Rep (advised (DepT e_ m)) ~ G.D1 x (G.C1 y advised_),
    DistributiveProduct e_ m advised_,
    Functor m
  ) =>
  DistributiveRecord e_ m advised
  where
  _distribute f =
    let advised_ = _distributeProduct @_ @e_ @m (fmap (fmap (G.unM1 . G.unM1 . G.from)) f)
     in G.to (G.M1 (G.M1 advised_))

instance
  ( DistributiveProduct e_ m advised_left,
    DistributiveProduct e_ m advised_right,
    Functor m
  ) =>
  DistributiveProduct e_ m (advised_left G.:*: advised_right)
  where
  _distributeProduct f  = 
      _distributeProduct @_ @e_ @m (fmap (fmap (\(l G.:*: _) -> l)) f) 
      G.:*: 
      _distributeProduct @_ @e_ @m (fmap (fmap (\(_ G.:*: r) -> r)) f) 

instance
  ( 
    Functor m, 
    Multicurryable as e_ m r advised
  ) =>
  DistributiveProduct e_ m (G.S1 ( 'G.MetaSel msymbol su ss ds) (G.Rec0 advised))
  where
  _distributeProduct f = G.M1 . G.K1 $ askFinalDepT @as @e_ @m @r (fmap (fmap (G.unK1 . G.unM1))  f)

-- advising *all* fields of a record
--
--
type AdvisedRecord :: (Type -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> (Type -> Constraint) -> ((Type -> Type) -> Type) -> Constraint
class AdvisedRecord ca e_ m cr advised where
  _adviseRecord :: [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca e_ m r) -> advised (DepT e_ m) -> advised (DepT e_ m)

type AdvisedProduct :: (Type -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> (Type -> Constraint) -> (k -> Type) -> Constraint
class AdvisedProduct ca e_ m cr advised_ where
  _adviseProduct :: TypeRep -> [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca e_ m r) -> advised_ k -> advised_ k

instance
  ( G.Generic (advised (DepT e_ m)),
    -- G.Rep (advised (DepT e_ m)) ~ G.D1 ('G.MetaData name mod p nt) (G.C1 y advised_),
    G.Rep (advised (DepT e_ m)) ~ G.D1 x (G.C1 y advised_),
    Typeable advised,
    AdvisedProduct ca e_ m cr advised_
  ) =>
  AdvisedRecord ca e_ m cr advised
  where
  _adviseRecord acc f unadvised =
    let G.M1 (G.M1 unadvised_) = G.from unadvised
        advised_ = _adviseProduct @_ @ca @e_ @m @cr (typeRep (Proxy @advised)) acc f unadvised_
     in G.to (G.M1 (G.M1 advised_))

instance
  ( AdvisedProduct ca e_ m cr advised_left,
    AdvisedProduct ca e_ m cr advised_right
  ) =>
  AdvisedProduct ca e_ m cr (advised_left G.:*: advised_right)
  where
  _adviseProduct tr acc f (unadvised_left G.:*: unadvised_right) = _adviseProduct @_ @ca @e_ @m @cr tr acc f unadvised_left G.:*: _adviseProduct @_ @ca @e_ @m @cr tr acc f unadvised_right

type DiscriminateAdvisedComponent :: Type -> RecordComponent
type family DiscriminateAdvisedComponent c where
  DiscriminateAdvisedComponent (a -> b) = Terminal
  DiscriminateAdvisedComponent (DepT e_ m x) = Terminal
  DiscriminateAdvisedComponent (Identity _) = IWrapped
  DiscriminateAdvisedComponent (I _) = IWrapped
  DiscriminateAdvisedComponent _ = Recurse

type AdvisedComponent :: RecordComponent -> (Type -> Constraint) -> ((Type -> Type) -> Type) -> (Type -> Type) -> (Type -> Constraint) -> Type -> Constraint
class AdvisedComponent component_type ca e_ m cr advised where
  _adviseComponent :: [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca e_ m r) -> advised -> advised

instance
  ( AdvisedComponent (DiscriminateAdvisedComponent advised) ca e_ m cr advised,
    KnownSymbol fieldName
  ) =>
  AdvisedProduct ca e_ m cr (G.S1 ( 'G.MetaSel ( 'Just fieldName) su ss ds) (G.Rec0 advised))
  where
  _adviseProduct tr acc f (G.M1 (G.K1 advised)) =
    let acc' = acc ++ [(tr, symbolVal (Proxy @fieldName))]
     in G.M1 (G.K1 (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @e_ @m @cr acc' f advised))

instance
  AdvisedRecord ca e_ m cr advisable =>
  AdvisedComponent Recurse ca e_ m cr (advisable (DepT e_ m))
  where
  _adviseComponent acc f advised = _adviseRecord @ca @e_ @m @cr acc f advised

instance
  (Multicurryable as e_ m r advised, All ca as, cr r, Monad m) =>
  AdvisedComponent Terminal ca e_ m cr advised
  where
  _adviseComponent acc f advised = advise @ca @e_ @m (f acc) advised

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca e_ m cr advised =>
  AdvisedComponent IWrapped ca e_ m cr (Identity advised)
  where
  _adviseComponent acc f (Identity advised) = Identity (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @e_ @m @cr acc f advised)

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca e_ m cr advised =>
  AdvisedComponent IWrapped ca e_ m cr (I advised)
  where
  _adviseComponent acc f (I advised) = I (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @e_ @m @cr acc f advised)

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
  forall ca cr e_ m advised.
  AdvisedRecord ca e_ m cr advised =>
  -- | The advice to apply.
  (forall r . cr r => [(TypeRep, String)] -> Advice ca e_ m r) ->
  -- | The record to advise recursively.
  advised (DepT e_ m) ->
  -- | The advised record.
  advised (DepT e_ m)
adviseRecord = _adviseRecord @ca @e_ @m @cr []

-- $records
--
-- 'adviseRecord' and 'deceiveRecord' are versions of 'advise' and 'deceive' that, instead of working on bare
-- functions, transform entire records-of-functions in one go. They also work
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
--   newtype Wraps x = Wraps x
--   env :: Env (DepT Env (Writer ()))
--   env =
--     let logger = Logger \_ -> pure ()
--         repository =
--           adviseRecord @Top @Top mempty $
--           deceiveRecord Wraps $
--           Repository {select = \_ -> pure [], insert = \_ -> pure ()}
--         controller =
--           adviseRecord @Top @Top mempty $
--           deceiveRecord Wraps $
--           Controller \_ -> pure "view"
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

-- $invocation
-- These functions are helpers for running 'DepT' computations, beyond what 'runDepT' provides.
--
-- They aren't directly related to 'Advice's, but they require some of the same machinery, and that's why they are here.

-- | An advice that is polymorphic on the environment (allowing it to unify
-- with 'Control.Monad.Dep.NilEnv') can be converted to a "simple" 'Control.Monad.Dep.SimpleAdvice.Advice' that doesn't require 'Control.Monad.Dep.DepT' at all. 
toSimple :: Monad m => Advice ca NilEnv m r -> SA.Advice ca m r
toSimple (Advice f) = SA.Advice \args -> lift do
    (withExecution, args') <- f args `runDepT` NilEnv
    let withExecution' = lift . flip runDepT NilEnv . withExecution . lift . SA.runAspectT
    pure (withExecution', args')

-- | Convert a simple 'Control.Monad.Dep.SimpleAdvice.Advice' which doesn't directly use the underlying monad @m@ into an 'Advice'.
fromSimple :: forall ca e_ m r. Monad m => (e_ (DepT e_ m) -> SA.Advice ca (DepT e_ m) r) -> Advice ca e_ m r
fromSimple makeAdvice = Advice \args -> do
    env <- ask
    case makeAdvice env of
        SA.Advice f -> do
            let SA.AspectT argsAction = f args
            (tweakExecution, args') <- argsAction
            pure (coerce tweakExecution, args')

