{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Control.Monad.Dep
import Control.Monad.Dep.Has
import Control.Monad.Dep.Advice
import Control.Monad.Dep.Advice.Basic
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Data.Kind
import Data.List (intercalate,lookup)
import Rank2 qualified
import Rank2.TH qualified
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (log)
import Data.Proxy
import System.IO
import qualified GHC.Generics as G
import System.IO
import Control.Exception
import Control.Arrow (Kleisli (..))
import Data.Text qualified as Text
import Data.Function ((&))
import Data.Functor ((<&>), ($>))
import Data.String

--
--
--

type Logger :: (Type -> Type) -> Type
newtype Logger d = Logger {
    info :: String -> d ()
  }

data Repository d = Repository
  { findById :: Int -> d (Maybe String)
  , putById :: Int -> String -> d ()
  , insert :: String -> d Int
  }

data Controller d = Controller 
  { create :: d Int
  , append :: Int -> String -> d Bool 
  , inspect :: Int -> d (Maybe String)
  } deriving G.Generic

type MessagePrefix = Text.Text

data LoggerConfiguration = LoggerConfiguration { 
        messagePrefix :: MessagePrefix
    } deriving stock (Show, Generic)
      deriving anyclass FromJSON

makeStdoutLogger :: MonadIO m => MessagePrefix -> env -> Logger m
makeStdoutLogger prefix _ = Logger (\msg -> liftIO (putStrLn (Text.unpack prefix ++ msg)))

makeInMemoryRepository 
    :: (Has Logger IO env, MonadIO m) 
    => IORef (Map Int String) 
    -> env 
    -> Repository m
makeInMemoryRepository ref (asCall -> call) = do
    Repository {
         findById = \key -> do
            call info "I'm going to do a lookup in the map!"
            theMap <- liftIO $ readIORef ref
            pure (Map.lookup key theMap)
       , putById = \key content -> do
            theMap <- liftIO $ readIORef ref
            liftIO $ writeIORef ref $ Map.insert key content theMap 
       , insert = \content -> do 
            call info "I'm going to insert in the map!"
            theMap <- liftIO $ readIORef ref
            let next = Map.size theMap
            liftIO $ writeIORef ref $ Map.insert next content theMap 
            pure next
    }

makeController :: forall m env . (Has Logger m env, Has Repository m env, Monad m) => env -> Controller m
makeController (asCall -> call) = Controller {
      create = do
          call info "Creating a new empty resource."
          key <- call insert ""
          pure key
    , append = \key extra -> do
          call info "Appending to a resource"
          mresource <- call findById key
          case mresource of
            Nothing -> do
                pure False
            Just resource -> do
                call putById key (resource ++ extra) 
                pure True
    , inspect = \key -> do
          call findById key 
    }

-- from purely Has-using to MonadDep-using
-- this is very verbose, how to automate it?
-- makeController'' :: forall e_ m . (Has Logger (DepT e_ m) (e_ (DepT e_ m)), Has Repository (DepT e_ m) (e_ (DepT e_ m)), Monad m) => Controller (DepT e_ m)
-- makeController'' = Controller {
--         create = askFinalDepT $ fmap create makeController
--       , append = askFinalDepT $ fmap append makeController
--       , inspect = askFinalDepT $ fmap inspect makeController
--     }

makeController''' :: forall e_ m . (Has Logger (DepT e_ m) (e_ (DepT e_ m)), Has Repository (DepT e_ m) (e_ (DepT e_ m)), Monad m) => Controller (DepT e_ m)
makeController''' = askForEnv makeController

type EnvHKD :: (Type -> Type) -> (Type -> Type) -> Type
data EnvHKD h m = EnvHKD
  { logger :: h (Logger m),
    repository :: h (Repository m),
    controller :: h (Controller m)
  } deriving stock Generic
    deriving anyclass (Phased, DemotableFieldNames, FieldsFindableByType)

deriving via Autowired (EnvHKD Identity m) instance Autowireable r_ m (EnvHKD Identity m) => Has r_ m (EnvHKD Identity m)

parseConf :: FromJSON a => Configurator a
parseConf = Kleisli parseJSON

type Configurator = Kleisli Parser Value 

type Allocator = ContT () IO

type Phases env_ m = Configurator `Compose` Allocator `Compose` DepT env_ m

env :: EnvHKD (Phases EnvHKD IO) IO
env = EnvHKD {
      logger = 
        parseConf `bindPhase` \(LoggerConfiguration {messagePrefix}) -> 
        skipPhase @Allocator $
        askForEnv (makeStdoutLogger messagePrefix)
    , repository = 
        skipPhase @Configurator $
        allocateMap `bindPhase` \ref -> 
        askForEnv (makeInMemoryRepository ref)
    , controller = 
        skipPhase @Configurator $
        skipPhase @Allocator $ 
        askForEnv makeController
}

tests :: TestTree
tests =
  testGroup
    "All"
    [
    ]

main :: IO ()
main = defaultMain tests
