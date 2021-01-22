{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

-- |
-- This module contains examples of simple advices.
--
-- __/BEWARE!/__ These are provided for illustrative purposes only, they
-- strive for simplicity and not robustness or efficiency.
module Control.Monad.Dep.Advice.Basic
  ( -- * Basic advices
    returnMempty,
    printArgs,
    AnyEq (..),
    doBadCaching
  )
where

import Control.Monad.Dep
import Control.Monad.Dep.Advice
import Control.Monad.IO.Class
import Control.Monad.Trans
import Data.Proxy
import Data.SOP
import Data.SOP (hctraverse_)
import Data.SOP.NP
import Data.Type.Equality
import System.IO
import Type.Reflection
import Control.Concurrent

-- | Makes functions discard their result and always return 'mempty'.
--
-- Because it doesn't touch the arguments or require some effect from the
-- environment, this 'Advice' is polymorphic on @ca@ and @cem@.
returnMempty :: forall ca cem. Advice ca cem Monoid
returnMempty =
  makeExecutionAdvice
    ( \action -> do
        _ <- action
        pure mempty
    )

-- | Given a 'Handle' and a prefix string, makes functions print their
-- arguments to the 'Handle'.
--
-- This advice uses 'BaseConstraint' to lift the 'MonadIO' constraint that
-- applies only to the monad.
--
-- Because it doesn't touch the return value of the advised function, this
-- 'Advice' is polymorphic on @cr@.
printArgs :: forall cr. Handle -> String -> Advice Show (BaseConstraint MonadIO) cr
printArgs h prefix =
  makeArgsAdvice
    ( \args -> do
        liftIO $ hPutStr h $ prefix ++ ":"
        hctraverse_ (Proxy @Show) (\(I a) -> liftIO (hPutStr h (" " ++ show a))) args
        liftIO $ hPutStrLn h "\n"
        liftIO $ hFlush h
        pure args
    )

-- | A helper datatype for universal equality comparisons of existentialized values, used by 'doBadCaching'.
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
-- Given functions for looking up and storing values in the underlying monad
-- @m@, makes functions (inefficiently) cache their results.
--
-- Notice the equality constraints on the 'Advice'. This means that the monad
-- @m@ and the result type @r@ are known and fixed before building the advice.
-- Once built, the 'Advice' won't be polymorphic over them.
--
-- The implementation of this function makes use of the existential type
-- parameter @u@ of 'makeAdvice', because the phase that processes the function
-- arguments needs to communicate the calculated cache key to the phase that
-- processes the function result.
doBadCaching :: forall m r. (AnyEq -> m (Maybe r)) -> (AnyEq -> r -> m ()) -> Advice (And Eq Typeable) (BaseConstraint ((~) m)) ((~) r)
doBadCaching cacheLookup cachePut =
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

doBadAsync :: Advice ca (BaseConstraint ((~) IO)) ((~) ())
doBadAsync = makeExecutionAdvice (\action -> do
        e <- ask 
        _ <- liftIO $ forkIO $ runDepT action e
        pure ()
    )

