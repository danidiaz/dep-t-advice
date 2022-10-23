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
module Dep.IOAdvice.Basic 
  ( -- * Basic advices
    returnMempty,
    printArgs,
  )
where

import Dep.IOAdvice
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
-- >>> import Dep.IOAdvice
-- >>> import Dep.IOAdvice.Basic
-- >>> import Control.Monad
-- >>> import Data.Kind
-- >>> import Data.SOP
-- >>> import Data.SOP.NP
-- >>> import Data.Monoid
-- >>> import System.IO
-- >>> import Data.IORef


-- | Makes functions discard their result and always return 'mempty'.
--
returnMempty :: forall ca r. Monoid r => Advice ca r
returnMempty =
  makeExecutionAdvice
    ( \action -> do
        _ <- action
        pure (mempty :: r)
    )

-- | Given a 'Handle' and a prefix string, makes functions print their
-- arguments to the 'Handle'.
--
printArgs :: forall r . Handle -> String -> Advice Show r
printArgs h prefix =
  makeArgsAdvice
    ( \args -> do
        hPutStr h $ prefix ++ ":"
        hctraverse_ (Proxy @Show) (\(I a) -> hPutStr h (" " ++ show a)) args
        hPutStrLn h "\n"
        hFlush h
        pure args
    )
