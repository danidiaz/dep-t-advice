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
module Control.Monad.Dep.SimpleAdvice.Basic
  ( -- * Basic advices
    returnMempty,
    printArgs,
    AnyEq (..),
    doCachingBadly,
    doAsyncBadly
  )
where

import Control.Monad.Dep
import Control.Monad.Dep.SimpleAdvice
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
-- >>> import Control.Monad.Dep.Advice.Basic (printArgs,returnMempty)
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
--
-- The @IO@ monad could be generalized to @MonadUnliftIO@.
doAsyncBadly :: forall ca . Advice ca IO ()
doAsyncBadly = makeExecutionAdvice \action -> do
    _ <- liftIO $ forkIO $ runAspectT action
    pure ()


