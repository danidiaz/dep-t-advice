{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Control.Arrow (Kleisli (..))
import Control.Exception
import Control.Monad.Dep
import Control.Monad.Dep.Class
import Control.Monad.IO.Unlift
import Control.Monad.Reader
import Control.Monad.Trans.Cont
import Control.Monad.Writer
import Data.Aeson
import Data.Aeson.Types
import Data.Coerce
import Data.Function ((&))
import Data.Functor (($>), (<&>))
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.IORef
import Data.Kind
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String
import Data.Text qualified as Text
import Data.Typeable
import Dep.Env
import Dep.Has
import Dep.SimpleAdvice
import Dep.SimpleAdvice.Basic
import GHC.Generics (Generic)
import GHC.TypeLits
import System.IO
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (insert, log, lookup)

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

type StackTrace = [(TypeRep, String)]

data SyntheticCallStackException
  = SyntheticCallStackException IOException StackTrace
  deriving stock (Eq, Show)

instance Exception SyntheticCallStackException

keepSyntheticStack ::
  (MonadUnliftIO m, MonadReader StackTrace m) =>
  NonEmpty (TypeRep, String) ->
  Advice ca m r
keepSyntheticStack (NonEmpty.head -> method) = makeExecutionAdvice \action -> do
  currentStack <- ask
  withRunInIO \unlift -> do
    er <- try @IOException (unlift (local (method :) action))
    case er of
      Left e -> throwIO (SyntheticCallStackException e (method : currentStack))
      Right r -> pure r

allocateBombs :: Int -> ContT () IO (IORef ([IO ()], [IO ()]))
allocateBombs i = ContT $ bracket (newIORef bombs) pure
  where
    bombs =
      ( replicate i (pure ()) ++ repeat (throwIO (userError "oops")),
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
        allocateBombs 1 `bindPhase` \ref ->
          constructor (\_ -> makeStdoutLogger)
            <&> advising
              ( adviseRecord @Top @Top \method ->
                  keepSyntheticStack method <> injectFailures ref
              ),
      repository =
        allocateSet `bindPhase` \ref ->
          constructor (makeInMemoryRepository ref)
            <&> advising
              ( adviseRecord @Top @Top \method ->
                  keepSyntheticStack method
              ),
      controller =
        skipPhase @Allocator $
          constructor makeController
            <&> advising
              ( adviseRecord @Top @Top \method ->
                  keepSyntheticStack method
              )
    }

--
--
--
--
testSyntheticCallStack :: Assertion
testSyntheticCallStack = do
  let action = 
          runContT (pullPhase @Allocator env) \constructors -> do
            let (asCall -> call) = fixEnv constructors
            flip
              runReaderT
              []
              ( do
                  _ <- call route 1 2
                  pure ()
              )
      expectedException = SyntheticCallStackException (userError "oops")
            [(typeRep (Proxy @Logger), "emitMsg")
            ,(typeRep (Proxy @Repository), "insert")
            ,(typeRep (Proxy @Controller), "route")]

  me <- try @SyntheticCallStackException action
  case me of 
    Left ex -> assertEqual "exception with callstack"  expectedException ex
    Right _ -> assertFailure "expected exception did not appear"

tests :: TestTree
tests =
  testGroup
    "All"
    [ testCase "synthetic call stack" testSyntheticCallStack
    ]

main :: IO ()
main = defaultMain tests
