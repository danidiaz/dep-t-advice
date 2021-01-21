{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}

-- | Some basic 'Advice's.
module Control.Monad.Dep.Advice.Basic where

import Control.Monad.Dep
import Control.Monad.Dep.Advice
import Control.Monad.IO.Class
import Data.Proxy
import Data.SOP
import Data.SOP (hctraverse_)
import Data.SOP.NP
import System.IO

-- | Makes the function discard its result and always return 'mempty'.
returnMempty :: Advice ca cem Monoid
returnMempty =
  makeExecutionAdvice
    ( \action -> do
        _ <- action
        pure mempty
    )

-- | Prints function arguments to a 'Handle'.
printArgs :: Handle -> String -> Advice Show (BaseConstraint MonadIO) cr
printArgs h prefix =
  makeArgsAdvice
    ( \args -> do
        liftIO $ hPutStr h $ prefix ++ ":"
        hctraverse_ (Proxy @Show) (\(I a) -> liftIO (hPutStr h (" " ++ show a))) args
        liftIO $ hFlush h
        pure args
    )

