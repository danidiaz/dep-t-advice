{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.Monad.Dep.SimpleAdvice.Internal where

import Data.Coerce
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Dep.Has
import Data.Functor.Identity
import Data.Kind
import Data.List.NonEmpty qualified as N
import Data.SOP
import Data.SOP.Dict
import Data.SOP.NP
import Data.Typeable
import GHC.Generics qualified as G
import GHC.TypeLits
import Control.Applicative
import Control.Monad.Cont.Class
import Control.Monad.Error.Class
import Control.Monad.IO.Unlift
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Writer.Class
import Control.Monad.Zip

-- | A generic transformation of 'AspectT'-effectful functions with environment
-- @e_@ of kind @(Type -> Type) -> Type@, base monad @m@ and return type @r@,
-- provided the functions satisfy certain constraint @ca@ of kind @Type ->
-- Constraint@ on all of their arguments.
--
-- Note that the type constructor for the environment @e_@ is given unapplied.
-- That is, @Advice Show NilEnv IO ()@ kind-checks but @Advice Show (NilEnv IO)
-- IO ()@ doesn't. See also 'Ensure'.
--
-- 'Advice's that don't care about the @ca@ constraint (because they don't
-- touch function arguments) can leave it polymorphic, and this facilitates
-- 'Advice' composition, but then the constraint must be given the catch-all
-- `Top` value (using a type application) at the moment of calling 'advise'.
--
-- See "Control.Monad.Dep.Advice.Basic" for examples.
type Advice ::
  (Type -> Constraint) ->
  (Type -> Type) ->
  Type ->
  Type
data Advice ca m r where
  Advice ::
    forall u ca m r.
    Proxy u ->
    ( forall as.
      All ca as =>
      NP I as ->
      AspectT m (u, NP I as)
    ) ->
    ( u ->
      AspectT m r ->
      AspectT m r
    ) ->
    Advice ca m r

type AspectT ::
  (Type -> Type) ->
  Type ->
  Type
newtype AspectT (m :: Type -> Type) (r :: Type) = AspectT {runAspectT :: m r}
  deriving
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadFix,
      MonadFail,
      MonadZip,
      MonadPlus,
      MonadCont,
      MonadIO,
      MonadUnliftIO
    )

instance MonadTrans AspectT where
  lift = AspectT 

deriving newtype instance MonadState s m => MonadState s (AspectT m)
deriving newtype instance MonadWriter w m => MonadWriter w (AspectT m)
deriving newtype instance MonadError e m => MonadError e (AspectT m)

