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
{-# LANGUAGE BlockArguments #-}

module Dep.SimpleAdvice.Internal where

import Dep.Has
import Data.Coerce
import Control.Monad
import Control.Monad.Fix
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
import Control.Monad.Reader
import Control.Monad.Cont.Class
import Control.Monad.Error.Class
import Control.Monad.IO.Unlift
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Writer.Class
import Control.Monad.Zip

-- | A generic transformation of 'AspectT'-effectful functions with 
-- base monad @m@ and return type @r@,
-- provided the functions satisfy certain constraint @ca@
-- on all of their arguments.
--
-- 'Advice's that don't care about the @ca@ constraint (because they don't
-- touch function arguments) can leave it polymorphic, and this facilitates
-- 'Advice' composition, but then the constraint must be given the catch-all
-- `Top` value (using a type application) at the moment of calling 'advise'.
--
-- See "Control.Monad.Dep.SimpleAdvice.Basic" for examples.
type Advice ::
  (Type -> Constraint) ->
  (Type -> Type) ->
  Type ->
  Type
data Advice (ca :: Type -> Constraint) m r where
  Advice ::
    forall ca m r.
    ( forall as.
      All ca as =>
      NP I as ->
      AspectT m (AspectT m r -> AspectT m r, NP I as)
    ) ->
    Advice ca m r


-- |
--    'Advice's compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'AspectT' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Monad m => Semigroup (Advice ca m r) where
  Advice outer <> Advice inner = Advice \args -> do
    (tweakOuter, argsOuter) <- outer args
    (tweakInner, argsInner) <- inner argsOuter
    pure (tweakOuter . tweakInner, argsInner)

instance Monad m => Monoid (Advice ca m r) where
  mappend = (<>)
  mempty = Advice \args -> pure (id, args)


-- | This transformer is isomorphic to 'Control.Monad.Trans.Identity.IdentityT'.
--
-- It doesn't really do anything, it only helps the typeclass machinery.
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

deriving newtype instance MonadReader env m => MonadReader env (AspectT m)
deriving newtype instance MonadState s m => MonadState s (AspectT m)
deriving newtype instance MonadWriter w m => MonadWriter w (AspectT m)
deriving newtype instance MonadError e m => MonadError e (AspectT m)

data Pair a b = Pair !a !b

