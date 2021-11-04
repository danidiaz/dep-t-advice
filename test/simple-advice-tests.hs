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

newtype Foo m = Foo { runFoo :: Int -> Bool -> m () } 
    deriving stock Generic

bareFoo :: MonadWriter [String] m => Int -> Bool -> m ()  
bareFoo = \_ _ -> tell ["foo"] 

foo :: MonadWriter [String] m => Foo m
foo = Foo bareFoo

someAdvice :: MonadWriter [String] m => Advice Top m r 
someAdvice = makeExecutionAdvice \action -> do
    tell ["before"]
    r <- action
    tell ["after"]
    pure r

--
--
tests :: TestTree
tests =
  testGroup
    "All"
    [
      testCase "adviseBare" $
        assertEqual "" ["before","foo","after"] $
            let advisedFunc = advise @Top someAdvice bareFoo
             in execWriter $ runAspectT $ advisedFunc 0 False
    , testCase "adviseRecord" $
        assertEqual "" ["before","foo","after"] $
          let advised = advising (adviseRecord @Top @Top \_ -> someAdvice) foo
           in execWriter $ runFoo advised 0 False
    ]

main :: IO ()
main = defaultMain tests
