{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Control.Arrow (Kleisli (..))
import Control.Exception
import Control.Monad.Dep (DepT)
import Control.Monad.IO.Unlift
import Control.Monad.Reader
import Control.Monad.Trans.Cont
import Data.Function ((&))
import Data.Functor (($>), (<&>))
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.IORef
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable
import Dep.Advice qualified as A
import Dep.Env
  ( Autowireable,
    Autowired (..),
    Constructor,
    DemotableFieldNames,
    FieldsFindableByType,
    Phased,
    bindPhase,
    constructor,
    fixEnv,
    pullPhase,
    skipPhase,
  )
import Dep.Has
  ( Has (dep),
    asCall,
  )
import Dep.SimpleAdvice
  ( Advice,
    AspectT (..),
    Top,
    adviseRecord,
    advising,
    makeExecutionAdvice,
  )
import Dep.SimpleAdvice.Basic (injectFailures)
import GHC.Generics (Generic)
import GHC.TypeLits
import Lens.Micro
import Lens.Micro.Extras
import System.IO
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (insert, lookup)

-- The interfaces
newtype Logger m = Logger
  { emitMsg :: String -> m ()
  }
  deriving stock (Generic)

data Repository m = Repository
  { insert :: Int -> m (),
    lookup :: Int -> m Bool
  }
  deriving stock (Generic)

newtype Controller m = Controller
  { -- insert one, lookup the other. Nonsensical, but good for an example.
    route :: Int -> Int -> m Bool
  }
  deriving stock (Generic)

-- The implementations

makeStdoutLogger :: MonadIO m => Logger m
makeStdoutLogger = Logger \msg -> liftIO $ putStrLn msg

allocateSet :: ContT () IO (IORef (Set Int))
allocateSet = ContT $ bracket (newIORef Set.empty) pure

makeInMemoryRepository ::
  (Has Logger m env, MonadIO m) =>
  IORef (Set Int) ->
  env ->
  Repository m
makeInMemoryRepository ref (asCall -> call) = do
  Repository
    { insert = \key -> do
        call emitMsg "inserting..."
        theSet <- liftIO $ readIORef ref
        liftIO $ writeIORef ref $ Set.insert key theSet,
      lookup = \key -> do
        call emitMsg "looking..."
        theSet <- liftIO $ readIORef ref
        pure (Set.member key theSet)
    }

makeController ::
  (Has Logger m env, Has Repository m env, Monad m) =>
  env ->
  Controller m
makeController (asCall -> call) =
  Controller
    { route = \toInsert toLookup -> do
        call emitMsg "serving..."
        call insert toInsert
        call lookup toLookup
    }

-- This is framework code.
--
-- It doesn't know about the exact datatypes the business logic uses,
-- or about the arity of methods in the business logic.
--
-- It can be reused accross applications.

type MethodName = String

type StackFrame = (TypeRep, MethodName)

type StackTrace = [StackFrame]

data SyntheticCallStackException
  = SyntheticCallStackException SomeException StackTrace
  deriving stock Show

instance Exception SyntheticCallStackException

class HasSyntheticCallStack e where
    callStack :: Lens' e StackTrace

instance HasSyntheticCallStack StackTrace  where
    callStack = id

keepCallStack ::
  (MonadUnliftIO m, MonadReader runenv m, HasSyntheticCallStack runenv, Exception e) =>
  (SomeException -> Maybe e) ->
  NonEmpty (TypeRep, MethodName) ->
  Advice ca m r
keepCallStack selector (NonEmpty.head -> method) = makeExecutionAdvice \action -> do
  currentStack <- asks (view callStack)
  withRunInIO \unlift -> do
    er <- tryJust selector (unlift (local (over callStack (method :)) action))
    case er of
      Left e -> throwIO (SyntheticCallStackException (toException e) (method : currentStack))
      Right r -> pure r

ioEx :: SomeException -> Maybe IOError
ioEx = fromException @IOError

allocateBombs :: Int -> ContT () IO (IORef ([IO ()], [IO ()]))
allocateBombs whenToBomb = ContT $ bracket (newIORef bombs) pure
  where
    bombs =
      ( replicate whenToBomb (pure ()) ++ repeat (throwIO (userError "oops")),
        repeat (pure ())
      )

-- Here we define our dependency injection environment.
--
-- We list which components from part of the application.
--
data Env h m = Env
  { logger :: h (Logger m),
    repository :: h (Repository m),
    controller :: h (Controller m)
  }
  deriving stock (Generic)
  deriving anyclass (Phased, DemotableFieldNames, FieldsFindableByType)

deriving via Autowired (Env Identity m) instance Autowireable r_ m (Env Identity m) => Has r_ m (Env Identity m)

-- The "phases" that components go through until fully build. Each phase
-- is represented as an applicative functor. The succession of phases is
-- defined using Data.Functor.Compose.
--

-- A phase in which we might allocate some resource needed by the component,
-- also set some bracket-like resource management.
type Allocator = ContT () IO

-- First we allocate any needed resource, then we have a construction phase
-- during which the component reads its own dependencies from the environment.
--
-- There could be more phases, like an initial "read configuration" phase for example.
type Phases env_ m = Allocator `Compose` Constructor env_ m

-- Environment value
--
env :: Env (Phases Env (ReaderT StackTrace IO)) (ReaderT StackTrace IO)
env =
  Env
    { logger =
        allocateBombs 1 `bindPhase` \bombs ->
          constructor (\_ -> makeStdoutLogger)
            <&> advising
              ( adviseRecord @Top @Top \method ->
                  keepCallStack ioEx method <> injectFailures bombs
              ),
      repository =
        allocateSet `bindPhase` \ref ->
          constructor (makeInMemoryRepository ref)
            <&> advising
              ( adviseRecord @Top @Top \method ->
                  keepCallStack ioEx method
              ),
      controller =
        skipPhase @Allocator $
          constructor makeController
            <&> advising
              ( adviseRecord @Top @Top \method ->
                  keepCallStack ioEx method
              )
    }

--
type Phases' = Allocator `Compose` Identity

data CallEnv i e_ m = CallEnv
  { _callInfo :: i,
    _ops :: e_ m
  }

instance Has r_ m (e_ m) => Has r_ m (CallEnv i e_ m) where
  dep = dep . _ops

instance HasSyntheticCallStack (CallEnv StackTrace e_ m) where
    callStack = lens _callInfo (\(CallEnv _ ops) i' -> CallEnv i' ops)

env' :: Env Phases' (DepT (CallEnv StackTrace (Env Identity)) IO)
env' =
  Env
    { logger =
        allocateBombs 1 `bindPhase` \bombs ->
          Identity (A.component (\_ -> makeStdoutLogger))
            <&> A.adviseRecord @Top @Top 
                \method ->
              A.fromSimple_ (keepCallStack ioEx method <> injectFailures bombs)
    , repository =
        allocateSet `bindPhase` \ref ->
          Identity (A.component (makeInMemoryRepository ref))
            <&> A.adviseRecord @Top @Top \method ->
              A.fromSimple_ (keepCallStack ioEx method)
    , controller =
        skipPhase @Allocator $
          Identity (A.component makeController)
            <&> A.adviseRecord @Top @Top \method ->
              A.fromSimple_ (keepCallStack ioEx method)
    }

--
--
--
--
expectedException :: (IOError, StackTrace)
expectedException =
    ( userError "oops"
    , [ (typeRep (Proxy @Logger), "emitMsg"),
        (typeRep (Proxy @Repository), "insert"),
        (typeRep (Proxy @Controller), "route")
      ]
    )

testSyntheticCallStack :: Assertion
testSyntheticCallStack = do
  let action =
        runContT (pullPhase @Allocator env) \constructors -> do
          let (asCall -> call) = fixEnv constructors
          flip
            runReaderT
            ([] :: StackTrace) -- the initial stack trace for the call
            ( do
                _ <- call route 1 2
                pure ()
            )
  me <- try @SyntheticCallStackException action
  case me of
    Left (SyntheticCallStackException (fromException @IOError -> Just ex) trace) -> 
        assertEqual "exception with callstack" expectedException (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

testSyntheticCallStack' :: Assertion
testSyntheticCallStack' = do
  let action =
        runContT (pullPhase @Allocator env') \runnable -> do
          _ <- A.runFromDep (pure (CallEnv [] runnable)) route 1 2
          pure ()
  me <- try @SyntheticCallStackException action
  case me of
    Left (SyntheticCallStackException (fromException @IOError -> Just ex) trace) -> 
        assertEqual "exception with callstack" expectedException (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

tests :: TestTree
tests =
  testGroup
    "All"
    [ testCase "synthetic call stack" testSyntheticCallStack,
      testCase "synthetic call stack - DepT" testSyntheticCallStack'
    ]

main :: IO ()
main = defaultMain tests
