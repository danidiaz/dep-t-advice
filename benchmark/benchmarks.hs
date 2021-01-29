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

module Main where

import Criterion.Main

import Control.Monad.Dep
import Control.Monad.Dep.Advice
import Control.Monad.Dep.Advice.Basic
import Data.Monoid
import Data.Functor.Identity
import Data.Foldable

-- returnMempty' :: forall ca e m r. (Monad m, Monoid r) => Advice ca e m r
-- returnMempty' =
--   makeAdvice @()
--     (\args -> pure (pure args))
--     ( \() action -> do
--         _ <- action
--         pure (mempty :: r)
--     )

mempty' :: forall ca e m r. Monad m => Advice ca e m r
mempty' = makeAdvice @()
  (\args -> pure (pure args))
  (\() -> id)

summy :: Monad m => Int -> Int -> Int -> Int -> DepT NilEnv m (Sum Int)
summy a1 a2 a3 a4 = pure $ Sum a1 <> Sum a2 <> Sum a3 <> Sum a4

summyInstrumented :: Monad m => Int -> Int -> Int -> Int -> DepT NilEnv m (Sum Int)
summyInstrumented = 
    advise @Top mempty summy

summyInstrumented' :: Monad m => Int -> Int -> Int -> Int -> DepT NilEnv m (Sum Int)
summyInstrumented' = 
    advise @Top mempty' summy

main :: IO ()
main =
  defaultMain
    [ bgroup
        "adviceOverhead"
        [ 
            bench "not instrumented" $ 
                whnf 
                (foldl' (+) 0 . take 100000 . map (\(a1, a2, a3, a4) -> runIdentity $ summy a1 a2 a3 a4 `runDepT` NilEnv))
                (repeat (0,0,0,0)),
            bench "instrumented id advice" $ 
                whnf 
                (foldl' (+) 0 . take 100000 . map (\(a1, a2, a3, a4) -> runIdentity $ summyInstrumented a1 a2 a3 a4 `runDepT` NilEnv)) 
                (repeat (0,0,0,0)),
            bench "instrumented locally defined id advice" $ 
                whnf 
                (foldl' (+) 0 . take 100000 . map (\(a1, a2, a3, a4) -> runIdentity $ summyInstrumented' a1 a2 a3 a4 `runDepT` NilEnv)) 
                (repeat (0,0,0,0))
        ]
    ] 

