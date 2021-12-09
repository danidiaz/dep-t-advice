{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

-- |
-- This module contains basic examples advices.
--
-- __/BEWARE!/__ These are provided for illustrative purposes only, they
-- strive for simplicity and not robustness or efficiency.
--
-- They can be converted to @DepT@-based 'Dep.Advice.Advice's using 'Dep.Advice.fromSimple'.
module Dep.SimpleAdvice.Basic
  ( -- * Basic advices
    returnMempty,
    printArgs,
    AnyEq (..),
    doCachingBadly,
    doAsyncBadly,
    injectFailures,
    -- ** Synthetic call stacks
    MethodName,
    StackFrame,
    SyntheticCallStack,
    HasSyntheticCallStack (..),
    SyntheticStackTrace,
    SyntheticStackTraceException (..),
    keepCallStack
  )
where

import Dep.SimpleAdvice
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Proxy
import Data.Functor.Constant
import Data.Functor.Identity
import Data.SOP
import Data.SOP (hctraverse_)
import Data.SOP.NP
import Data.Type.Equality
import Data.Coerce
import System.IO
import Control.Concurrent
import Control.Monad.IO.Unlift
import Data.IORef
import Control.Exception
import Type.Reflection
import qualified Data.Typeable as T
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Control.Monad.Dep (DepT)
import Data.Functor.Const

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
-- >>> import Control.Monad.Trans
-- >>> import Dep.SimpleAdvice
-- >>> import Dep.SimpleAdvice.Basic (printArgs,returnMempty)
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef



-- | Makes functions discard their result and always return 'mempty'.
--
returnMempty :: forall ca m r. (Monad m, Monoid r) => Advice ca m r
returnMempty =
  makeExecutionAdvice
    ( \action -> do
        _ <- action
        pure (mempty :: r)
    )

-- | Given a 'Handle' and a prefix string, makes functions print their
-- arguments to the 'Handle'.
--
printArgs :: forall m r. MonadIO m => Handle -> String -> Advice Show m r
printArgs h prefix =
  makeArgsAdvice
    ( \args -> do
        liftIO $ hPutStr h $ prefix ++ ":"
        hctraverse_ (Proxy @Show) (\(I a) -> liftIO (hPutStr h (" " ++ show a))) args
        liftIO $ hPutStrLn h "\n"
        liftIO $ hFlush h
        pure args
    )

-- | A helper datatype for universal equality comparisons of existentialized values, used by 'doCachingBadly'.
--
-- For a more complete elaboration of this idea, see the the \"exinst\" package.
data AnyEq where
  AnyEq :: forall a. (Typeable a, Eq a) => a -> AnyEq

instance Eq AnyEq where
  AnyEq any1 == AnyEq any2 =
    case testEquality (typeOf any1) (typeOf any2) of
      Nothing -> False
      Just Refl -> any1 == any2

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
doCachingBadly :: forall m r. Monad m => (AnyEq -> m (Maybe r)) -> (AnyEq -> r -> m ()) -> Advice (Eq `And` Typeable) m r
doCachingBadly cacheLookup cachePut = makeAdvice \args ->
        let key = AnyEq $ cfoldMap_NP (Proxy @(And Eq Typeable)) (\(I a) -> [AnyEq a]) $ args
            tweakExecution action = do
                mr <- lift $ cacheLookup key
                case mr of
                  Nothing -> do
                    r <- action
                    lift $ cachePut key r
                    pure r
                  Just r ->
                    pure r
         in pure (tweakExecution, args)

-- | Makes functions that return `()` launch asynchronously.
--
-- A better implementation of this advice would likely use the \"async\"
-- package instead of bare `forkIO`. 
doAsyncBadly :: forall ca m . MonadUnliftIO m => Advice ca m ()
doAsyncBadly = makeExecutionAdvice \action -> do
    _ <- withRunInIO (\unlift -> forkIO (unlift action))
    pure ()


-- | Given a reference with two infinite lists of 'IO' actions, on each
-- invocation of the advised function, take an action from the first list and
-- execute it before, and take one action from the second list and execute it
-- after.
--
-- A common use for this would be to pass exception-throwing actions.
injectFailures :: forall ca m r . (MonadIO m, MonadFail m) => IORef ([IO ()], [IO ()]) -> Advice ca m r
injectFailures ref = makeExecutionAdvice \action -> do
    (before, after) <- liftIO $ atomicModifyIORef' ref \(before : befores, after : afters) -> ((befores, afters), (before, after))
    liftIO before
    r <- action
    liftIO after
    pure r


-- Synthetic call stacks
--


type MethodName = String

-- | The typeable representation of the record which contains the invoked
-- function, along with the field name of the invoked function.
type StackFrame = NonEmpty (T.TypeRep, MethodName)

type SyntheticCallStack = [StackFrame]

type SyntheticStackTrace = NonEmpty StackFrame

-- | Wraps an exception along with a 'SyntheticCallStack'.
data SyntheticStackTraceException
  = SyntheticStackTraceException SomeException SyntheticStackTrace
  deriving stock Show

instance Exception SyntheticStackTraceException

-- | Monads that carry a SyntheticCallStack.
class MonadCallStack m where
  askCallStack :: m SyntheticCallStack
  addStackFrame :: StackFrame -> m r -> m r

instance (Monad m, HasSyntheticCallStack runenv) => MonadCallStack (ReaderT runenv m) where
  askCallStack = asks (view callStack)
  addStackFrame frame action = local (over callStack (frame :)) action

instance (Monad m, HasSyntheticCallStack (e_ (DepT e_ m))) => MonadCallStack (DepT e_ m) where
  askCallStack = asks (view callStack)
  addStackFrame frame action = local (over callStack (frame :)) action

deriving newtype instance MonadCallStack m => MonadCallStack (AspectT m)

-- | Class of environments that carry a 'SyntheticCallStack' value that can be
-- modified.
class HasSyntheticCallStack e where
    -- | A lens from the environment to the call stack.
    callStack :: forall f . Functor f => (SyntheticCallStack -> f SyntheticCallStack) -> e -> f e

-- | The trivial case, useful when 'SyntheticCallStack' is the environment type
-- of a 'Control.Monad.Reader.ReaderT'.
instance HasSyntheticCallStack SyntheticCallStack where
    callStack = id

instance HasSyntheticCallStack s => HasSyntheticCallStack (Const s x) where
    callStack f = fmap Const . callStack f . getConst


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
  (MonadUnliftIO m, MonadCallStack m, Exception e) =>
  -- | A selector for the kinds of exceptions we want to catch.
  -- For example @fromException \@IOError@.
  (SomeException -> Maybe e) ->
  -- | The path to the current component/method in the environment.
  -- It will be usually obtained through
  -- 'Dep.SimpleAdvice.adviseRecord'.
  NonEmpty (T.TypeRep, MethodName) ->
  Advice ca m r
keepCallStack selector method = makeExecutionAdvice \action -> do
  currentStack <- askCallStack
  withRunInIO \unlift -> do
    er <- tryJust selector (unlift (addStackFrame method action))
    case er of
      Left e -> throwIO (SyntheticStackTraceException (toException e) (method :| currentStack))
      Right r -> pure r


view :: ((a1 -> Constant a1 b1) -> a2 -> Constant c b2) -> a2 -> c
view l = getConstant . l Constant

over :: ((a1 -> Identity a2) -> a3 -> Identity c) -> (a1 -> a2) -> a3 -> c
over l f = runIdentity . l (Identity . f)

