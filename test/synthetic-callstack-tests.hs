{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
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
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveAnyClass #-}

module Main (main) where

import Control.Arrow (Kleisli (..))
import Control.Exception
import Control.Monad.Dep
import Control.Monad.Dep.Class
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
import GHC.Generics (Generic)
import GHC.TypeLits
import System.IO
import Test.Tasty
import Test.Tasty.HUnit
import Data.Typeable
import Prelude hiding (insert, log, lookup)

-- The interfaces
newtype Logger m = Logger
  { emitMsg :: String -> m ()
  } deriving stock Generic

data Repository m = Repository
  { insert :: Int -> m (),
    lookup :: Int -> m Bool
  } deriving stock Generic

data Controller m = Controller
  { -- insert one, lookup the other. Nonsensical, but good for an example.
    route :: Int -> Int -> m Bool
  } deriving stock Generic

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

-- The environment
--

data Env h m = Env {
        logger :: h (Logger m)
    ,   repository :: h (Repository m)
    ,   controller :: h (Controller m)
    }
    deriving stock Generic
    deriving anyclass (Phased, DemotableFieldNames, FieldsFindableByType)

deriving via Autowired (Env Identity m) instance Autowireable r_ m (Env Identity m) => Has r_ m (Env Identity m)

-- 
--
type Configurator = Kleisli Parser Value

parseConf :: FromJSON a => Configurator a
parseConf = Kleisli parseJSON

type Allocator = ContT () IO

type Phases env_ m = Allocator `Compose` Constructor env_ m

-- 
--

type StackTrace = [(TypeRep, String)]

-- Environment value
--
bombAt :: Int -> ContT () IO (IORef ([IO ()], [IO ()]))
bombAt i = ContT $ bracket (newIORef bombs) pure
    where
    bombs = ( replicate i (pure ()) ++ repeat (throwIO (userError "oops"))
            , repeat (pure ())
            )

env :: Env (Phases Env (ReaderT StackTrace IO)) (ReaderT StackTrace IO)
env = Env {
      logger = 
        bombAt 1 `bindPhase` \ref ->
        constructor (\_ -> makeStdoutLogger) 
            <&> advising (adviseRecord @Top @Top (\_ -> injectFailures ref))    
    , repository = 
        allocateSet `bindPhase` \ref -> 
        constructor (makeInMemoryRepository ref)
    , controller = 
        skipPhase $
        constructor makeController
    }

--
--
--
tests :: TestTree
tests =
  testGroup
    "All"
    []

main :: IO ()
main = defaultMain tests
