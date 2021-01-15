{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Control.Monad.Dep
import Control.Monad.Reader
import Data.Kind
import Rank2 qualified
import Rank2.TH qualified
import Prelude hiding (log)

-- The environment doesn't know about any concrete monad
type Env :: (Type -> Type) -> Type
data Env m = Env
  { _logger :: String -> m (),
    _repository :: Int -> m (),
    _controller :: Int -> m Int
  }
$(Rank2.TH.deriveFunctor ''Env)

-- Has-style typeclasses can be provided to avoid depending on concrete
-- environments.
-- Note that the environment determines the monad.
type HasLogger :: Type -> (Type -> Type) -> Constraint
class HasLogger r m | r -> m where
  logger :: r -> String -> m ()

-- If our environment is parmeterized by the monad m, then logging is done in
-- m.
instance HasLogger (Env m) m where
  logger = _logger

type HasRepository :: Type -> (Type -> Type) -> Constraint
class HasRepository r m | r -> m where
  repository :: r -> Int -> m ()

instance HasRepository (Env m) m where
  repository = _repository

-- These two functions don't know the concrete envionment record.
--
-- This one because it only needs MonadIO.
mkStdoutLogger :: MonadIO m => String -> m ()
mkStdoutLogger msg = liftIO (putStrLn msg)

mkRepository :: (MonadReader e m, HasLogger e m) => Int -> m () 
mkRepository entity = do
  doLog <- reader logger
  doLog "I'm going to write the entity!"

-- This one because it receives a getter for the logger
-- A HasX-style typeclass would have been an alternative.
mkController :: (MonadReader e m, HasLogger e m, HasRepository e m) => Int -> m Int
mkController x = do
  doLog <- reader logger
  doLog "I'm going to insert in the db!"
  insert <- reader repository
  insert x
  return $ x * x

-- This is the first time DepT is used in this module.
-- Note that it is only here where we settle for IO.
env :: Env (DepT Env IO)
env =
  let _logger = mkStdoutLogger
      _controller = mkController
      _repository = mkRepository
   in Env {_logger, _controller, _repository}

-- We select "controller" as the entrypoint and run it.
result :: IO Int
result = runDepT (_controller env 7) env

-- The environment doesn't know about any concrete monad
type BiggerEnv :: (Type -> Type) -> Type
data BiggerEnv m = BiggerEnv
  { _inner :: Env m,
    _extra :: Int -> m Int
  }
$(Rank2.TH.deriveFunctor ''BiggerEnv)

biggerEnv :: BiggerEnv (DepT BiggerEnv IO)
biggerEnv =
  let -- _inner = (Rank2.<$>) (withDepT (Rank2.<$>) inner) env,
      _inner' = zoomEnv (Rank2.<$>) _inner env
      _extra = pure
   in BiggerEnv {_inner = _inner', _extra}

main :: IO ()
main = do
  r <- runDepT ((_controller . _inner $ biggerEnv) 7) biggerEnv
  print r

