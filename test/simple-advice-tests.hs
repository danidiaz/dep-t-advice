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
{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Prelude hiding (log)
import Barbies
import Control.Monad.Dep
import Control.Monad.Dep.SimpleAdvice
import Control.Monad.Dep.Advice (toSimple)
import Control.Monad.Dep.Advice.Basic
import Control.Monad.Dep.Has
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Coerce
import Data.Functor.Identity
import Data.Kind
import Data.List (intercalate)
import Data.SOP
import GHC.Generics
import Test.Tasty
import Test.Tasty.HUnit
import Data.IORef
import System.IO

-- the "component" we want to decorate
newtype Foo m = Foo { runFoo :: Int -> Bool -> m () } 
                deriving stock Generic

fooFunc :: MonadWriter [String] m => Int -> Bool -> m ()  
fooFunc = \_ _ -> tell ["foo"] 

foo :: MonadWriter [String] m => Foo m
foo = Foo fooFunc

-- works with functions of any number of arguments
someAdvice :: MonadWriter [String] m => Advice Top m r 
someAdvice = makeExecutionAdvice \action -> do
    tell ["before"]
    r <- action
    tell ["after"]
    pure r

advisedFoo :: MonadWriter [String] m => Foo m
advisedFoo = advising (adviseRecord @Top @Top \_ -> someAdvice) foo

-- Unlike regular advices, which require decorated
-- functions to be sufficiently polymorphic,
-- "simple" advices can decorate
-- non-DepT *concrete* monads.
concreteFoo :: IORef [String] -> Foo IO
concreteFoo ref = Foo \_ _ -> modifyIORef ref (\xs -> xs ++ ["foo"])

refAdvice :: MonadIO m => IORef [String] -> Advice Top m r 
refAdvice ref = makeExecutionAdvice \action -> do
    liftIO $ modifyIORef ref (\xs -> xs ++ ["before"])
    r <- action
    liftIO $ modifyIORef ref (\xs -> xs ++ ["after"])
    pure r

concreteAdvisedFoo :: IORef [String] -> Foo IO
concreteAdvisedFoo ref =
    advising (adviseRecord @Top @Top \_ -> refAdvice ref) (concreteFoo ref)

printAdvisedFoo :: IORef [String] -> Foo IO
printAdvisedFoo ref =
    advising (adviseRecord @_ @Top (\_ -> toSimple (printArgs stdout "args: "))) (concreteFoo ref)

--
--
tests :: TestTree
tests =
  testGroup
    "All"
    [
      testCase "adviseBare" $
        assertEqual "" ["before","foo","after"] $
            let advisedFunc = advise @Top someAdvice fooFunc
             in execWriter $ runAspectT $ advisedFunc 0 False
    , testCase "adviseRecord" $
        assertEqual "" ["before","foo","after"] $
          let advised = advising (adviseRecord @Top @Top \_ -> someAdvice) foo
           in execWriter $ runFoo advised 0 False
    , testCase "concrete adviseRecord" $ do
        ref <- newIORef []
        () <- runFoo (concreteAdvisedFoo ref) 0 False
        result <- readIORef ref
        assertEqual "" ["before","foo","after"] result
    , testCase "print adviseRecord" $ do
        ref <- newIORef []
        () <- runFoo (printAdvisedFoo ref) 0 False
        result <- readIORef ref
        assertEqual "" ["foo"] result
    ]

main :: IO ()
main = defaultMain tests
