{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}


-- |
-- This module contains examples of simple advices.
--
-- __/BEWARE!/__ These are provided for illustrative purposes only, they
-- strive for simplicity and not robustness or efficiency.
module Control.Monad.Dep.Advice.Basic
  ( -- * Basic advices
    returnMempty,
    printArgs,
    doLocally,
    AnyEq (..),
    doCachingBadly,
    doAsyncBadly
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
-- >>> import Control.Monad.Dep.Advice.Basic (printArgs,returnMempty)
-- >>> import Data.Constraint
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef



-- | Makes functions discard their result and always return 'mempty'.
--
-- Because it doesn't touch the arguments or require some effect from the
-- environment, this 'Advice' is polymorphic on @ca@ and @cem@.
returnMempty :: forall ca e m r. (Monad m, Monoid r) => Advice ca e m r
returnMempty =
  makeExecutionAdvice
    ( \action -> do
        _ <- action
        pure (mempty :: r)
    )

-- | Given a 'Handle' and a prefix string, makes functions print their
-- arguments to the 'Handle'.
--
-- This advice uses 'MonadConstraint' to lift the 'MonadIO' constraint that
-- applies only to the monad.
--
-- Because it doesn't touch the return value of the advised function, this
-- 'Advice' is polymorphic on @cr@.
printArgs :: forall e m r. MonadIO m => Handle -> String -> Advice Show e m r
printArgs h prefix =
  makeArgsAdvice
    ( \args -> do
        liftIO $ hPutStr h $ prefix ++ ":"
        hctraverse_ (Proxy @Show) (\(I a) -> liftIO (hPutStr h (" " ++ show a))) args
        liftIO $ hPutStrLn h "\n"
        liftIO $ hFlush h
        pure args
    )

-- | Use 'local' on the final 'DepT' action of a function.
--
-- Allows tweaking the environment that will be seen by the function and all of
-- its sub-calls.
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
doLocally :: forall ca e m r. Monad m => (forall n. e n -> e n) -> Advice ca e m r 
doLocally transform = makeExecutionAdvice (local transform)  


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
-- Given the means for looking up and storing values in the underlying monad
-- @m@, makes functions (inefficiently) cache their results.
--
-- Notice the equality constraints on the 'Advice'. This means that the monad
-- @m@ and the result type @r@ are known and fixed before building the advice.
-- Once built, the 'Advice' won't be polymorphic over them.
--
-- The implementation of this function makes use of the existential type
-- parameter @u@ of 'makeAdvice', because the phase that processes the function
-- arguments needs to communicate the calculated `AnyEq` cache key to the phase
-- that processes the function result.
--
-- A better implementation of this advice would likely use an @AnyHashable@
-- helper datatype for the keys.
doCachingBadly :: forall e m r. Monad m => (AnyEq -> m (Maybe r)) -> (AnyEq -> r -> m ()) -> Advice (Eq `And` Typeable) e m r
doCachingBadly cacheLookup cachePut =
  makeAdvice @AnyEq
    ( \args ->
        let key = AnyEq $ cfoldMap_NP (Proxy @(And Eq Typeable)) (\(I a) -> [AnyEq a]) $ args
         in pure (key, args)
    )
    ( \key action -> do
        mr <- lift $ cacheLookup key
        case mr of
          Nothing -> do
            r <- action
            lift $ cachePut key r
            pure r
          Just r ->
            pure r
    )

-- | Makes functions that return `()` launch asynchronously.
--
-- A better implementation of this advice would likely use the \"async\"
-- package instead of bare `forkIO`. 
--
-- And the @MustBe IO@ constraint could be relaxed to @MonadUnliftIO@.
doAsyncBadly :: forall ca e. Advice ca e IO ()
doAsyncBadly = makeExecutionAdvice (\action -> do
        e <- ask 
        _ <- liftIO $ forkIO $ runDepT action e
        pure ()
    )


