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

import Barbies
import Dep.Advice
import Dep.Has
import Control.Monad.Dep
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Coerce
import Data.Functor.Identity
import Data.Kind
import Data.List (intercalate)
import Data.SOP
import GHC.Generics
import Rank2 qualified
import Rank2.TH qualified
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (log)

-- https://stackoverflow.com/questions/53498707/cant-derive-generic-for-this-type/53499091#53499091
-- There are indeed some higher kinded types for which GHC can currently derive Generic1 instances, but the feature is so limited it's hardly worth mentioning. This is mostly an artifact of taking the original implementation of Generic1 intended for * -> * (which already has serious limitations), turning on PolyKinds, and keeping whatever sticks, which is not much.
type Logger :: (Type -> Type) -> Type
newtype Logger d = Logger {log :: String -> d ()} deriving (Generic)

instance FunctorB Logger

instance Dep Logger where
  type DefaultFieldName Logger = "logger"

type Repository :: (Type -> Type) -> Type
data Repository d = Repository
  { select :: String -> d [Int],
    insert :: [Int] -> d ()
  }
  deriving (Generic)

instance FunctorB Repository

instance Dep Repository where
  type DefaultFieldName Repository = "repository"

type Controller :: (Type -> Type) -> Type
newtype Controller d = Controller {serve :: Int -> d String} deriving (Generic)

instance FunctorB Controller

instance Dep Controller where
  type DefaultFieldName Controller = "controller"

type Env :: (Type -> Type) -> Type
data Env m = Env
  { logger :: Logger m,
    repository :: Repository m,
    controller :: Controller m
  }

instance Has Logger m (Env m)

instance Has Repository m (Env m)

instance Has Controller m (Env m)

-- dumb wrapper newtype
newtype Wraps x = Wraps x

env :: Env (DepT Env (Writer ()))
env =
  let logger = Logger \_ -> pure ()
      repository =
        adviseRecord @Top @Top mempty $
          deceiveRecord Wraps $
            Repository {select = \_ -> pure [], insert = \_ -> pure ()}
      controller =
        adviseRecord @Top @Top mempty $
          deceiveRecord Wraps $
            Controller \_ -> pure "view"
   in Env {logger, repository, controller}

ran :: Writer () String
ran = runFromDep (pure env) serve 7

--
-- to test the coercible in the definition of Has
type EnvHKD :: (Type -> Type) -> (Type -> Type) -> Type
data EnvHKD h m = EnvHKD
  { logger :: h (Logger m),
    repository :: h (Repository m),
    controller :: h (Controller m)
  }
  deriving (Generic)

instance Functor h => FunctorB (EnvHKD h)

instance FunctorT EnvHKD

instance TraversableT EnvHKD

instance Has Logger m (EnvHKD I m)

instance Has Repository m (EnvHKD I m)

instance Has Controller m (EnvHKD I m)

instance Has Repository m (EnvHKD Identity m)

instance Has Controller m (EnvHKD Identity m)

envHKD :: EnvHKD I (DepT Env (Writer ()))
envHKD =
  let logger =
        I $ Logger \_ -> pure ()
      repository =
        I $
          adviseRecord @Top @Top mempty $
            deceiveRecord Wraps $
              Repository {select = \_ -> pure [], insert = \_ -> pure ()}
      controller =
        I $
          adviseRecord @Top @Top mempty $
            deceiveRecord Wraps $
              Controller \_ -> pure "view"
   in adviseRecord @Top @Top mempty $ EnvHKD {logger, repository, controller}

-- modified as a whole
envHKD' :: EnvHKD I (DepT Env (Writer ()))
envHKD' =
  let logger =
        I $ Logger \_ -> pure ()
      repository =
        I $
          Repository {select = \_ -> pure [], insert = \_ -> pure ()}
      controller =
        I $
          Controller \_ -> pure "view"
   in adviseRecord @Top @Top mempty $
        deceiveRecord Wraps $
          EnvHKD {logger, repository, controller}

envHKDIdentity :: EnvHKD Identity (DepT Env (Writer ()))
envHKDIdentity =
  let logger =
        Identity $ Logger \_ -> pure ()
      repository =
        Identity $
          adviseRecord @Top @Top mempty $
            deceiveRecord Wraps $
              Repository {select = \_ -> pure [], insert = \_ -> pure ()}
      controller =
        Identity $
          adviseRecord @Top @Top mempty $
            deceiveRecord Wraps $
              Controller \_ -> pure "view"
   in adviseRecord @Top @Top mempty $ EnvHKD {logger, repository, controller}

-- modified as a whole
envHKDIdentity' :: EnvHKD Identity (DepT Env (Writer ()))
envHKDIdentity' =
  let logger =
        Identity $ Logger \_ -> pure ()
      repository =
        Identity $
          Repository {select = \_ -> pure [], insert = \_ -> pure ()}
      controller =
        Identity $
          Controller \_ -> pure "view"
   in adviseRecord @Top @Top mempty $
        deceiveRecord Wraps $
          EnvHKD {logger, repository, controller}

--
--
tests :: TestTree
tests =
  testGroup
    "All"
    []

main :: IO ()
main = defaultMain tests
