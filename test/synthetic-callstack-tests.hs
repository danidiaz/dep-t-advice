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

module Main (main) where

import Prelude hiding (insert, lookup)
import Control.Arrow (Kleisli (..))
import Control.Exception
import Control.Monad.Dep
import Control.Monad.Dep.Class
import Control.Monad.Reader
import Control.Monad.Trans.Cont
import Control.Monad.Writer
import Data.Coerce
import Data.Function ((&))
import Data.Functor (($>), (<&>))
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.IORef
import Data.Kind
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.SOP
import Data.Text qualified as Text
import Data.Typeable
import Dep.Has
import Dep.SimpleAdvice
import Dep.SimpleAdvice.Basic
import GHC.Generics
import System.IO
import Test.Tasty
import Test.Tasty.HUnit

-- The interfaces
newtype Logger m = Logger
  { emitMsg :: String -> m ()
  }

data Repository m = Repository
  { insert :: Int -> m (),
    lookup :: Int -> m Bool
  }

data Controller m = Controller
  { -- insert one, lookup the other. Nonsensical, but good for an example.
    route :: Int -> Int -> m Bool
  }

-- The implementations

makeStdoutLogger :: MonadIO m => Logger m
makeStdoutLogger = Logger \msg -> liftIO $ putStrLn msg

allocateMap :: ContT () IO (IORef (Set Int))
allocateMap = ContT $ bracket (newIORef Set.empty) pure

makeInMemoryRepository 
    :: (Has Logger m env, MonadIO m)
    => IORef (Set Int) 
    -> env 
    -> Repository m
makeInMemoryRepository ref (asCall -> call) = do
    Repository {
         insert = \key -> do
            call emitMsg "inserting..."
            theSet <- liftIO $ readIORef ref
            liftIO $ writeIORef ref $ Set.insert key theSet
       , lookup = \key -> do
            call emitMsg "looking..."
            theSet <- liftIO $ readIORef ref
            pure (Set.member key theSet)
    }

makeController 
    :: (Has Logger m env, Has Repository m env, Monad m)
    => env ->
    Controller m
makeController (asCall -> call) = Controller {
        route = \toInsert toLookup -> do
            call emitMsg "serving..."
            call insert toInsert
            call lookup toLookup
            
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
