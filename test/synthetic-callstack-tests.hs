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

-- | An example of how an application can make use of the "dep-t" and
-- "dep-t-advice" packages for keeping a "synthetic" call stack that tracks the
-- invocations of monadic functions.
--
-- We are assuming that the application follows a "record-of-functions" style.
module Main (main) where

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
import Dep.SimpleAdvice.Basic 
  (
    MethodName,
    StackFrame,
    StackTrace,
    SyntheticCallStackException (SyntheticCallStackException),
    HasSyntheticCallStack (callStack),
    keepCallStack
  )
import Dep.SimpleAdvice.Basic (injectFailures)
import GHC.Generics (Generic)
import GHC.TypeLits
import Lens.Micro (Lens', lens)
import System.IO
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (insert, lookup)


-- THE BUSINESS LOGIC
--
--

-- Component interfaces, defined as records polymorphic over the effect monad.
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
  { -- insert one arg, look up the other. Nonsensical, but good enough for an example.
    route :: Int -> Int -> m Bool
  }
  deriving stock (Generic)

-- Component implementations, some of which depend on other componets.
--
makeStdoutLogger :: MonadIO m => Logger m
makeStdoutLogger = Logger \msg -> liftIO $ putStrLn msg

-- allocation helper
allocateSet :: ContT () IO (IORef (Set Int))
allocateSet = ContT $ bracket (newIORef Set.empty) pure

-- When a component depends on another, it does so by taking an "env" parameter
-- in the constructor and requiring 'Has' constraints on it.
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

-- This implementation of Controller depends both on the Logger and the
-- Repository.
--
-- In general, the graph of dependencies between components can be a complex
-- directed acyclic graph.
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

-- THE COMPOSITION ROOT
--
-- Here we define our dependency injection environment.
--
-- We put all the components which will form part of our application in an
-- environment record. 
--
-- Each field is wrapped in a functor `h` which controls the "phases" we must
-- go through in  the construction of the environment.
data Env h m = Env
  { logger :: h (Logger m),
    repository :: h (Repository m),
    controller :: h (Controller m)
  }
  deriving stock (Generic)
  deriving anyclass (Phased, DemotableFieldNames, FieldsFindableByType)

-- Locate the components by their types. We could also define the required Has
-- instance for each component manually.
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
-- There could be more phases, like for example an initial "read configuration"
-- phase.
type Phases env_ m = Allocator `Compose` Constructor env_ m

-- Environment value
--
-- The base monad is a 'ReaderT' holding a StackTrace value which gets modified
-- using "local" for each sub-call.
--
-- Notice that neither the interfaces nor the implementations which we defined
-- earlier knew anything about the ReaderT.
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

-- Catch only IOExceptions for this example.
ioEx :: SomeException -> Maybe IOError
ioEx = fromException @IOError

-- Allocate a supply of potentially exception-throwing actions.
allocateBombs :: Int -> ContT () IO (IORef ([IO ()], [IO ()]))
allocateBombs whenToBomb = ContT $ bracket (newIORef bombs) pure
  where
    bombs =
      ( replicate whenToBomb (pure ()) ++ repeat (throwIO (userError "oops")),
        repeat (pure ())
      )


-- THE COMPOSITION ROOT - ALTERNATIVE APPROACH
--
--
-- Here we'll define the dependency injection environment in a slightly
-- different way (but reusing both the "business logic" and the Env type).

-- The basic idea is that we don't perform dependency injection as a separate
-- Applicative phase (so no Constructor, but a mere Indentity phase). 
--
-- Instead, we shift that task into the base monad's environent. 

-- As a result the "phases" are simpler:
type Phases' = Allocator `Compose` Identity

-- Now the expanded "runtime" environment will hold both the StackTrace and the
-- components. We define this small helper datatype for that. It augments a
-- preexisting environment with call-related info.
data CallEnv i e_ m = CallEnv
  { _callInfo :: i,
    _ops :: e_ m
  }

-- Delegate all 'Has' queries to the inner environment.
instance Has r_ m (e_ m) => Has r_ m (CallEnv i e_ m) where
  dep = dep . _ops

instance HasSyntheticCallStack (CallEnv StackTrace e_ m) where
    callStack = lens _callInfo (\(CallEnv _ ops) i' -> CallEnv i' ops)

-- Here use the DepT monad (a variant of ReaderT) as the base monad.
--
-- The environment of DepT includes—just as before—the StackTrace value that is
-- used to track each sub-call.
--
-- But now it also includes the dependency injection context with all the
-- components.
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

-- TESTS
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

-- Test the" Constructor"-based version of the environment.
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

-- Test the "DepT"-based version of the environment.
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
