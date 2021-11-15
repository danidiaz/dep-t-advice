{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}


-- |
-- This module contains basic examples advices.
--
-- __/BEWARE!/__ These are provided for illustrative purposes only, they
-- strive for simplicity and not robustness or efficiency.
module Control.Monad.Dep.Advice.Basic
  ( -- * Basic advices
    doLocally
  )
where

import Control.Monad.Dep
import Control.Monad.Dep.Advice
import Data.Proxy
import Data.SOP
import Data.SOP (hctraverse_)
import Data.SOP.NP
import Data.Type.Equality
import System.IO
import Type.Reflection
import Control.Concurrent

-- $setup
--
-- >>> :set -XTypeApplications
-- >>> :set -XStandaloneKindSignatures
-- >>> :set -XMultiParamTypeClasses
-- >>> :set -XFunctionalDependencies
-- >>> :set -XRankNTypes
-- >>> :set -XTypeOperators
-- >>> :set -XConstraintKinds
-- >>> :set -XNamedFieldPuns
-- >>> :set -XFlexibleContexts
-- >>> :set -XFlexibleInstances
-- >>> :set -XAllowAmbiguousTypes
-- >>> :set -XBlockArguments
-- >>> import Control.Monad
-- >>> import Control.Monad.Dep
-- >>> import Control.Monad.Dep.Advice
-- >>> import Control.Monad.Dep.Advice.Basic
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef


-- | Use 'local' on the final 'DepT' action of a function.
--
-- Allows tweaking the environment that will be seen by the function and all of
-- its sub-calls into dependencies. 
--
-- Perhaps this is __not__ what you want; often, it's better to tweak
-- the environment for the current function only. For those cases,
-- 'Control.Monad.Dep.Advice.deceive' might be a better fit. 
--
-- >>> :{
--  type HasLogger :: Type -> (Type -> Type) -> Constraint
--  class HasLogger em m | em -> m where
--    logger :: em -> String -> m ()
--  type Env :: (Type -> Type) -> Type
--  data Env m = Env
--    { _logger1 :: String -> m (),
--      _logger2 :: String -> m (),
--      _controllerA :: Int -> m (),
--      _controllerB :: Int -> m ()
--    }
--  instance HasLogger (Env m) m where
--    logger = _logger1
--  envIO :: Env (DepT Env IO)
--  envIO = Env 
--    {
--      _logger1 = 
--          \_ -> liftIO $ putStrLn "logger1 ran",
--      _logger2 = 
--          \_ -> liftIO $ putStrLn "logger2 ran",
--      _controllerA = 
--          \_ -> do e <- ask; logger e "foo",
--      _controllerB = 
--          advise @Top 
--          (doLocally \e@Env{_logger2} -> e {_logger1 = _logger2}) 
--          \_ -> do e <- ask; logger e "foo" 
--    }
-- :}
--
--  >>> runFromEnv (pure envIO) _controllerA 0
--  logger1 ran
--
--  >>> runFromEnv (pure envIO) _controllerB 0
--  logger2 ran
--
doLocally :: forall ca e_ m r. Monad m => (e_ (DepT e_ m) -> e_ (DepT e_ m)) -> Advice ca e_ m r 
doLocally transform = makeExecutionAdvice (local transform)  


