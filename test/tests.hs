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

module Main (main) where

import Control.Monad.Dep
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
import Data.Function ((&))

-- Some helper typeclasses.
--
-- Has-style typeclasses can be provided to avoid depending on concrete
-- environments.
-- Note that the environment determines the monad.
type HasLogger :: (Type -> Type) -> Type -> Constraint
class HasLogger d r | r -> d where
  logger :: r -> String -> d ()

-- Possible convenience function to avoid having to use ask before logging
-- Worth the extra boilerplate, or not?
loggerD :: MonadDep '[HasLogger] d e m => String -> m ()
loggerD msg = asks logger >>= \f -> liftD $ f msg

type HasRepository :: (Type -> Type) -> Type -> Constraint
class HasRepository d r | r -> d where
  repository :: r -> Int -> d ()

-- Some possible implementations.
--
-- An implementation of the controller, done programming against interfaces
-- (well, against typeclasses).
-- Polymorphic on the monad.
mkController :: MonadDep [HasLogger, HasRepository] d e m => Int -> m String
mkController x = do
  e <- ask
  liftD $ logger e "I'm going to insert in the db!"
  liftD $ repository e x
  return "view"

-- A "real" logger implementation that interacts with the external world.
mkStdoutLogger :: MonadIO m => String -> m ()
mkStdoutLogger msg = liftIO (putStrLn msg)

-- A "real" repository implementation
mkStdoutRepository :: (MonadDep '[HasLogger] d e m, MonadIO m) => Int -> m ()
mkStdoutRepository entity = do
  e <- ask
  liftD $ logger e "I'm going to write the entity!"
  liftIO $ print entity

-- The traces we accumulate from the fakes during tests
type TestTrace = ([String], [Int])

-- A "fake". A pure implementation for tests.
mkFakeLogger :: Monoid x => MonadWriter ([String],x) m => String -> m ()
mkFakeLogger msg = tell ([msg], mempty)

-- Ditto.
mkFakeRepository :: (MonadDep '[HasLogger] d e m, MonadWriter TestTrace m) => Int -> m ()
mkFakeRepository entity = do
  e <- ask
  liftD $ logger e "I'm going to write the entity!"
  tell ([], [entity])

--
--
-- Here we define a monomorphic environment working on IO
type EnvIO :: Type
data EnvIO = EnvIO
  { _loggerIO :: String -> IO (),
    _repositoryIO :: Int -> IO ()
  }

instance HasLogger IO EnvIO where
  logger = _loggerIO

instance HasRepository IO EnvIO where
  repository = _repositoryIO

-- In the monomorphic environment, the controller function lives "separate",
-- having access to the logger and the repository through the ReaderT
-- environment.
--
-- The question is: the repository function *also* needs to know about the
-- logger!  Shouldn't it be aware of the ReaderT environment as well? Why
-- privilege the controller function in such a manner?
--
-- In a sufficiently complex app, the diverse functions will form a DAG of
-- dependencies between each other. So it would be nice if the functions were
-- treated uniformly, all having access to (views of) the environment record.
mkControllerIO :: (HasLogger IO e, HasRepository IO e) => Int -> ReaderT e IO String
mkControllerIO x = do
  e <- ask
  liftIO $ logger e "I'm going to insert in the db!"
  liftIO $ repository e x
  return "view"

--
--
-- Here we define some polymorphic environments, which are basically
-- records-of-functions parameterized by an effect monad.
type Env :: (Type -> Type) -> Type
data Env m = Env
  { _logger :: String -> m (),
    _repository :: Int -> m (),
    _controller :: Int -> m String
  }

$(Rank2.TH.deriveFunctor ''Env)

-- If our environment is parmeterized by the monad m, then logging is done in
-- m.
instance HasLogger m (Env m) where
  logger = _logger

instance HasRepository m (Env m) where
  repository = _repository

-- This bigger environment is for demonstrating how to "nest" environments.
type BiggerEnv :: (Type -> Type) -> Type
data BiggerEnv m = BiggerEnv
  { _inner :: Env m,
    _extra :: Int -> m Int
  }

$(Rank2.TH.deriveFunctor ''BiggerEnv)

--
--
-- Creating environment values and commiting to a concrete monad.
--
-- This is the first time DepT is used in this module.
-- Note that it is only here where we settle for a concrete monad for the
-- polymorphic environments.
env :: Env (DepT Env (Writer TestTrace))
env =
  let _logger = mkFakeLogger
      _repository = mkFakeRepository
      _controller = mkController
   in Env {_logger, _repository, _controller}

-- An IO variant
envIO :: Env (DepT Env IO)
envIO =
  let _logger = mkStdoutLogger
      _repository = mkStdoutRepository
      _controller = mkController
   in Env {_logger, _repository, _controller}

biggerEnv :: BiggerEnv (DepT BiggerEnv (Writer TestTrace))
biggerEnv =
  let -- We embed the small environment into the bigger one using "zoomEnv"
      -- and the rank-2 fmap that allows us to change the monad which
      -- parameterized the environment.
      --
      -- _inner' = (Rank2.<$>) (withDepT (Rank2.<$>) inner) env,
      _inner' = zoomEnv (Rank2.<$>) _inner env
      _extra = pure
   in BiggerEnv {_inner = _inner', _extra}

biggerEnvIO :: BiggerEnv (DepT BiggerEnv IO)
biggerEnvIO =
  let _inner' = zoomEnv (Rank2.<$>) _inner envIO
      _extra = pure
   in BiggerEnv {_inner = _inner', _extra}

expected :: TestTrace
expected = (["I'm going to insert in the db!", "I'm going to write the entity!"], [7])

--
--
-- Experiment about adding instrumetation

doLogging :: forall e m r. (HasLogger m e, Monad m) => e -> Advice Show m r
doLogging e = makeAdvice \args -> do
    let args' = cfoldMap_NP (Proxy @Show) (\(I a) -> [show a]) args
    lift $ logger e $ "advice before: " ++ intercalate "," args'
    let tweakAction action = do
            e <- ask
            r <- action
            lift $ logger e $ "advice after"
            pure r
    pure (tweakAction, args)

advicedEnv :: Env (DepT Env (Writer TestTrace))
advicedEnv = env & advising \env ->
   env {
         _controller = advise (popAdvice doLogging) (_controller env)
       }

expectedAdviced :: TestTrace
expectedAdviced = (["advice before: 7", "I'm going to insert in the db!", "I'm going to write the entity!", "advice after"], [7])

-- a small test of constraint composition
weirdAdvicedEnv :: Env (DepT Env (Writer TestTrace))
weirdAdvicedEnv =
   env {
         _controller = advise (doLogging <> returnMempty) (_controller env), --,
         -- This advice below doesn't really do anything, I'm just experimenting with passing the constraints with type application
         _logger = advise @(Show `And` Eq) (makeAdvice @() (\args -> pure (pure args)) (\_ -> id)) (_logger env)
       }

-- type EnsureLoggerAndWriter :: ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
-- type EnsureLoggerAndWriter = Ensure HasLogger `And2` MonadConstraint (MonadWriter TestTrace)

-- to ways to invoke restrict functions
-- doLogging':: Advice Show EnsureLoggerAndWriter cr
-- doLogging'= restrictEnv (Sub Dict) doLogging
-- 
-- doLogging'' = restrictEnv @EnsureLoggerAndWriter (Sub Dict) doLogging
 
-- Checking that constraints on the environment and the monad are collected "automatically"
doLogging' :: forall e m r . (HasLogger m e, HasRepository m e, MonadIO m) => e -> Advice Show m r
doLogging' = doLogging 

justARepositoryConstraint :: forall ca e m r. (HasRepository m e, Monad m) => e -> Advice ca m r
justARepositoryConstraint _ = mempty

doLogging'' :: forall e m r . (HasLogger m e, HasRepository m e, MonadIO m) => e -> Advice Show m r
doLogging'' _ = doLogging <> justARepositoryConstraint

-- Checking that constraints on the results are collected "automatically"
returnMempty' :: forall ca m r. (Monad m, Monoid r, Show r, Read r) => Advice ca m r
returnMempty' = returnMempty

justAResultConstraint :: forall ca e m r. (Monad m, Show r, Read r) => e -> Advice ca m r
justAResultConstraint = mempty

returnMempty'' :: forall ca e m r. (Monad m, Monoid r, Show r, Read r) => e -> Advice ca m r
returnMempty'' _ = returnMempty <> justAResultConstraint e

printArgs' = restrictArgs @(Eq `And` Ord `And` Show) (\Dict -> Dict) (printArgs @NilEnv @IO stdout "foo")
 
-- does EnvConstraint compile?

-- type FooAdvice = Advice Top (EnvConstraint (MustBe NilEnv)) Top


--
--
-- environment for testing ba

data CachingTestEnv m = CachingTestEnv { 
    _cacheTestLogic :: m (),
    _expensiveComputation :: Int -> Bool -> m String,
    _logger2 :: String -> m ()
    }

instance HasLogger m (CachingTestEnv m) where
  logger = _logger2

type HasExpensiveComputation :: (Type -> Type) -> Type -> Constraint
class HasExpensiveComputation d r | r -> d where
  expensiveComputation :: r -> Int -> Bool -> d String
instance HasExpensiveComputation m (CachingTestEnv m) where
  expensiveComputation = _expensiveComputation 

mkFakeExpensiveComputation :: MonadDep '[HasLogger] d e m => Int -> Bool -> m String
mkFakeExpensiveComputation i b = do
    e <- ask
    liftD $ logger e "Doing expensive computation"
    return $ (show i ++ show b)

cacheTestLogic :: MonadDep [HasLogger, HasExpensiveComputation] d e m => m ()
cacheTestLogic = do
    e <- ask
    liftD $ expensiveComputation e 0 False >>= logger e
    liftD $ expensiveComputation e 1 True >>= logger e
    liftD $ expensiveComputation e 0 False >>= logger e
    liftD $ expensiveComputation e 1 True >>= logger e

type ExpensiveComputationMonad = RWS () ([String],()) [(AnyEq,String)]

cacheLookup :: AnyEq -> ExpensiveComputationMonad (Maybe String)
cacheLookup key = do
    cache <- get
    pure $ lookup key cache

cachePut :: AnyEq -> String -> ExpensiveComputationMonad ()
cachePut key v = modify ((key,v) :)

cacheTestEnv :: CachingTestEnv (DepT CachingTestEnv ExpensiveComputationMonad)
cacheTestEnv = CachingTestEnv {
        _cacheTestLogic = cacheTestLogic,
        _expensiveComputation = advise (doCachingBadly cacheLookup cachePut) mkFakeExpensiveComputation,
        _logger2 = mkFakeLogger
    }

expectedCached :: ([String],())
expectedCached = (["Doing expensive computation","0False","Doing expensive computation","1True","0False","1True"],())

--
--
--

tests :: TestTree
tests =
  testGroup
    "All"
    [ testCase "hopeThisWorks" $
        assertEqual "" expected $
          execWriter $ runDepT (do e <- ask; (_controller . _inner) e 7) biggerEnv,
      testCase "hopeAOPWorks" $
        assertEqual "" expectedAdviced $
          execWriter $ runDepT (do e <- ask; _controller e 7) advicedEnv,
      testCase "hopeCachingWorks" $
        assertEqual "" expectedCached $
          let action = runFromEnv (pure cacheTestEnv) _cacheTestLogic 
              (_,w) = execRWS action () mempty
           in w
    ]

main :: IO ()
main = defaultMain tests
