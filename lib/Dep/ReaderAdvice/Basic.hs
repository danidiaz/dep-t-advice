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
module Dep.ReaderAdvice.Basic 
  ( -- * Basic advices
    returnMempty,
    printArgs,
    -- ** Synthetic call stacks
    Simple.MethodName,
    Simple.StackFrame,
    Simple.SyntheticCallStack,
    Simple.HasSyntheticCallStack (..),
    Simple.SyntheticStackTrace,
    Simple.SyntheticStackTraceException (..),
    keepCallStack
  )
where

import Dep.ReaderAdvice
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
import Data.IORef
import Dep.SimpleAdvice.Basic qualified as Simple
import Dep.SimpleAdvice.Basic (HasSyntheticCallStack)

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
-- >>> import Dep.ReaderAdvice
-- >>> import Dep.ReaderAdvice.Basic
-- >>> import Control.Monad
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef


-- | Makes functions discard their result and always return 'mempty'.
--
returnMempty :: forall ca env m r. (Monad m, Monoid r) => Advice ca env m r
returnMempty =
  makeExecutionAdvice
    ( \action -> do
        _ <- action
        pure (mempty :: r)
    )

-- | Given a 'Handle' and a prefix string, makes functions print their
-- arguments to the 'Handle'.
--
printArgs :: forall env m r. MonadIO m => Handle -> String -> Advice Show env m r
printArgs h prefix =
  makeArgsAdvice
    ( \args -> do
        liftIO $ hPutStr h $ prefix ++ ":"
        hctraverse_ (Proxy @Show) (\(I a) -> liftIO (hPutStr h (" " ++ show a))) args
        liftIO $ hPutStrLn h "\n"
        liftIO $ hFlush h
        pure args
    )


-- | If the environment carries a 'SyntheticCallStack', make advised functions add
-- themselves to the 'SyntheticCallStack' before they start executing.
--
-- Caught exceptions are rethrown wrapped in 'SyntheticStackTraceException's,
-- with the current 'SyntheticCallStack' added.
keepCallStack ::
  (MonadUnliftIO m, Simple.HasSyntheticCallStack env, Exception e) =>
  -- | A selector for the kinds of exceptions we want to catch.
  -- For example @ fromException \@IOError@.
  (SomeException -> Maybe e) ->
  -- | The path to the current component/method in the environment.
  -- It will be usually obtained through
  -- 'Dep.ReaderAdvice.adviseRecord'.
  NonEmpty (T.TypeRep, Simple.MethodName) ->
  Advice ca env m r
keepCallStack selector method = makeExecutionAdvice \action -> do
  currentStack <- Simple.askCallStack
  withRunInIO \unlift -> do
    er <- tryJust selector (unlift (Simple.addStackFrame method action))
    case er of
      Left e -> throwIO (Simple.SyntheticStackTraceException (toException e) (method :| currentStack))
      Right r -> pure r
