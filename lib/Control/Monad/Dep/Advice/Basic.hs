{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}

-- | 
-- This module contains examples of simple advices.
module Control.Monad.Dep.Advice.Basic
  ( -- * Basic advices
    returnMempty,
    printArgs,
  )
where

import Control.Monad.Dep
import Control.Monad.Dep.Advice
import Control.Monad.IO.Class
import Data.Proxy
import Data.SOP
import Data.SOP (hctraverse_)
import Data.SOP.NP
import System.IO

-- | Makes the function discard its result and always return 'mempty'.
--
-- Because it doesn't touch the arguments or require some effect from the
-- environment, this advice is polymorphic on @ca@ and @cem@.
returnMempty :: forall ca cem. Advice ca cem Monoid
returnMempty =
  makeExecutionAdvice
    ( \action -> do
        _ <- action
        pure mempty
    )

-- | Prints function arguments to a 'Handle'.
--
-- This advice uses 'BaseConstraint' to lift the 'MonadIO' constraint that
-- applies only to the monad.
--
-- Because it doesn't touch the return value of the advised function, this
-- advice is polymorphic on @cr@.
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
