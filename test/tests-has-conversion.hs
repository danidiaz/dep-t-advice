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

-- makeInMemoryRepository 
--     :: Has Logger IO env 
--     => IORef (Map Int String) 
--     -> env 
--     -> Repository IO
-- makeInMemoryRepository ref (asCall -> call) = do
--     Repository {
--          findById = \key -> do
--             call info "I'm going to do a lookup in the map!"
--             theMap <- readIORef ref
--             pure (Map.lookup key theMap)
--        , putById = \key content -> do
--             theMap <- readIORef ref
--             writeIORef ref $ Map.insert key content theMap 
--        , insert = \content -> do 
--             call info "I'm going to insert in the map!"
--             theMap <- readIORef ref
--             let next = Map.size theMap
--             writeIORef ref $ Map.insert next content theMap 
--             pure next
--     }

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
makeController'' :: forall e_ m . (Has Logger (DepT e_ m) (e_ (DepT e_ m)), Has Repository (DepT e_ m) (e_ (DepT e_ m)), Monad m) => Controller (DepT e_ m)
makeController'' = Controller {
        create = askFinalDepT $ fmap create makeController
      , append = askFinalDepT $ fmap append makeController
      , inspect = askFinalDepT $ fmap inspect makeController
    }

makeController''' :: forall e_ m . (Has Logger (DepT e_ m) (e_ (DepT e_ m)), Has Repository (DepT e_ m) (e_ (DepT e_ m)), Monad m) => Controller (DepT e_ m)
makeController''' =
    strangeFixRecord makeController


tests :: TestTree
tests =
  testGroup
    "All"
    [
    ]

main :: IO ()
main = defaultMain tests
