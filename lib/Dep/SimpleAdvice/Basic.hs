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
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

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
    StackTrace,
    SyntheticCallStackException (..),
    HasSyntheticCallStack (..),
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
import System.IO
import Control.Concurrent
import Control.Monad.IO.Unlift
import Data.IORef
import Control.Exception
import Type.Reflection
import qualified Data.Typeable as T
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty

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
type MethodName = String

type StackFrame = (T.TypeRep, MethodName)

type StackTrace = [StackFrame]

data SyntheticCallStackException
  = SyntheticCallStackException SomeException StackTrace
  deriving stock Show

instance Exception SyntheticCallStackException

class HasSyntheticCallStack e where
    -- | A lens from the environment to the call stack.
    callStack :: forall f . Functor f => (StackTrace -> f StackTrace) -> e -> f e

instance HasSyntheticCallStack StackTrace  where
    callStack = id

keepCallStack ::
  (MonadUnliftIO m, MonadReader runenv m, HasSyntheticCallStack runenv, Exception e) =>
  (SomeException -> Maybe e) ->
  NonEmpty (T.TypeRep, MethodName) ->
  Advice ca m r
keepCallStack selector (NonEmpty.head -> method) = makeExecutionAdvice \action -> do
  currentStack <- asks (view callStack)
  withRunInIO \unlift -> do
    er <- tryJust selector (unlift (local (over callStack (method :)) action))
    case er of
      Left e -> throwIO (SyntheticCallStackException (toException e) (method : currentStack))
      Right r -> pure r
  where
  view l = getConstant . l Constant
  over l f = runIdentity . l (Identity . f)



