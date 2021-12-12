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
{-# LANGUAGE FlexibleContexts #-}


-- |
-- This module contains basic examples advices.
--
-- __/BEWARE!/__ These are provided for illustrative purposes only, they
-- strive for simplicity and not robustness or efficiency.
module Dep.Advice.Basic
  ( -- * Basic advices
    returnMempty,
    printArgs,
    SA.AnyEq (..),
    doCachingBadly,
    doAsyncBadly,
    injectFailures,
    doLocally,
    -- ** Synthetic call stacks
    SA.MethodName,
    SA.StackFrame,
    SA.SyntheticCallStack,
    SA.HasSyntheticCallStack (..),
    SA.SyntheticStackTrace,
    SA.SyntheticStackTraceException (..),
    SA.MonadCallStack (..),
    keepCallStack
  )
where

import Dep.Advice
import qualified Dep.SimpleAdvice.Basic as SA 
import Control.Monad.Dep
import Data.Proxy
import Data.SOP
import Data.SOP (hctraverse_)
import Data.SOP.NP
import Data.Type.Equality
import System.IO
import Type.Reflection
import Control.Concurrent
import Control.Monad.IO.Unlift
import Control.Exception
import qualified Data.Typeable as T
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import qualified Dep.SimpleAdvice.Basic as SA
import Data.IORef

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
-- >>> import Dep.Advice
-- >>> import Dep.Advice.Basic
-- >>> import Control.Monad
-- >>> import Control.Monad.Dep
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

-- | Makes functions discard their result and always return 'mempty'.
--
returnMempty :: forall ca e_ m r. (Monad m, Monoid r) => Advice ca e_ m r
returnMempty = fromSimple_ SA.returnMempty

-- | Given a 'Handle' and a prefix string, makes functions print their
-- arguments to the 'Handle'.
--
printArgs :: forall e_ m r. (Monad m, MonadIO (DepT e_ m)) => Handle -> String -> Advice Show e_ m r
printArgs h prefix = fromSimple_ (SA.printArgs h prefix)

-- | 
-- Given the means for looking up and storing @r@ values in the underlying
-- monad @m@, makes functions (inefficiently) cache their results.
--
-- The monad @m@ and the result type @r@ must be known before building the
-- advice. So, once built, this 'Advice' won't be polymorphic over them.
--
-- The implementation of this function makes use of the existential type
-- parameter @u@ of 'makeAdvice', because the phase that processes the function
-- arguments needs to communicate the calculated `AnyEq` cache key to the phase
-- that processes the function result.
--
-- A better implementation of this advice would likely use an @AnyHashable@
-- helper datatype for the keys.
doCachingBadly :: forall e_ m r. Monad m => (SA.AnyEq -> DepT e_ m (Maybe r)) -> (SA.AnyEq -> r -> DepT e_ m ()) -> Advice (Eq `And` Typeable) e_ m r
doCachingBadly cacheLookup cachePut = fromSimple_ (SA.doCachingBadly cacheLookup cachePut)

-- | Makes functions that return `()` launch asynchronously.
--
-- A better implementation of this advice would likely use the \"async\"
-- package instead of bare `forkIO`. 
doAsyncBadly :: forall ca e_ m . (Monad m, MonadUnliftIO (DepT e_ m)) => Advice ca e_ m ()
doAsyncBadly = fromSimple_ SA.doAsyncBadly

-- | Given a reference with two infinite lists of 'IO' actions, on each
-- invocation of the advised function, take an action from the first list and
-- execute it before, and take one action from the second list and execute it
-- after.
--
-- A common use for this would be to pass exception-throwing actions.
injectFailures :: forall ca e_ m r . (Monad m, MonadIO (DepT e_ m), MonadFail (DepT e_ m)) => IORef ([IO ()], [IO ()]) -> Advice ca e_ m r
injectFailures ref = fromSimple_ (SA.injectFailures ref)

-- | If the environment carries a 'SyntheticCallStack', make advised functions add
-- themselves to the 'SyntheticCallStack' before they start executing.
--
-- This 'Dep.SimpleAdvice.Advice' requires a reader-like base monad to work. It
-- doesn't need to be 'Control.Monad.Dep.DepT', it can be regular a
-- 'Control.Monad.Reader.ReaderT'.
--
-- Caught exceptions are rethrown wrapped in 'SyntheticStackTraceException's,
-- with the current 'SyntheticCallStack' added.
keepCallStack ::
  (Monad m, MonadUnliftIO (DepT e_ m), SA.MonadCallStack (DepT e_ m), Exception e) =>
  -- | A selector for the kinds of exceptions we want to catch.
  -- For example @fromException \@IOError@.
  (SomeException -> Maybe e) ->
  -- | The path to the current component/method in the environment.
  -- It will be usually obtained through
  -- 'Dep.SimpleAdvice.adviseRecord'.
  NonEmpty (T.TypeRep, SA.MethodName) ->
  Advice ca e_ m r
keepCallStack selector method = fromSimple_ (SA.keepCallStack selector method)