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

-- | 
-- This module provides the 'Advice' datatype, along for functions for creating,
-- manipulating, composing and applying values of that type.
--
-- 'Advice's represent generic transformations on effectful functions of
-- any number of arguments.
--
-- >>> :{
--    foo0 :: DepT NilEnv IO (Sum Int)
--    foo0 = pure (Sum 5)
--    foo1 :: Bool -> DepT NilEnv IO (Sum Int)
--    foo1 _ = foo0
--    foo2 :: Char -> Bool -> DepT NilEnv IO (Sum Int)
--    foo2 _ = foo1
-- :}
--
-- They work for monadic actions of zero arguments:
--
-- >>> advise (printArgs stdout "foo0") foo0 `runDepT` NilEnv
-- foo0:
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- And for functions of one or more arguments, provided they end on a monadic action:
--
-- >>> advise (printArgs stdout "foo1") foo1 False `runDepT` NilEnv
-- foo1: False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- >>> advise (printArgs stdout "foo2") foo2 'd' False `runDepT` NilEnv
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 5}
--
-- 'Advice's can also tweak the result value of functions:
--
-- >>> advise (returnMempty @Top) foo2 'd' False `runDepT` NilEnv
-- Sum {getSum = 0}
--
-- And they can be combined using @Advice@'s 'Monoid' instance before being
-- applied:
--
-- >>> advise (printArgs stdout "foo2" <> returnMempty) foo2 'd' False `runDepT` NilEnv
-- foo2: 'd' False
-- <BLANKLINE>
-- Sum {getSum = 0}
--
-- Although sometimes composition might require harmonizing the constraints
-- each 'Advice' places on the arguments, if they differ.
--
-- __NOTE__:
--
-- This modue is an alternative to "Control.Monad.Dep.Advice" with two advantages:
--
-- - It doesn't use 'Control.Monad.Dep.DepT'. The types are simpler because
--   they don't need to refer to 'Control.Monad.Dep.DepT''s environment.
--
-- - Unlike in "Control.Monad.Dep.Advice", we can advise functions / components
--   which work on a fixed concrete monad like 'IO'.
module Control.Monad.Dep.Advize
  ( -- * Preparing components for being advised
--    advising,
--    AspectT (..),
--    -- * The Advice type
    Advice,
    AspectT (..),
    makeAdvice,
--
--    -- * Creating Advice values
--    makeAdvice,
--    makeArgsAdvice,
--    makeExecutionAdvice,
--
--    -- * Applying Advices
--    advise,
--
--    -- * Harmonizing Advice argument constraints
--    -- $restrict
--    restrictArgs,
--
--    -- * Advising entire records
--    -- $records
--    adviseRecord,

    -- * "sop-core" re-exports
    -- $sop
    Top,
    And,
    All,
    NP (..),
    I (..),
    cfoldMap_NP,
    Dict (..),
  )
where

import Data.Coerce
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Dep
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

type Advice ::
  (Type -> Constraint) ->
  (Type -> Type) ->
  Type ->
  Type
data Advice ca m r where
  Advice ::
    forall ca m r.
    ( forall as.
      All ca as =>
      NP I as ->
      AspectT m (AspectT m r -> AspectT m r, NP I as)
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

deriving newtype instance MonadReader env m => MonadReader env (AspectT m)
deriving newtype instance MonadState s m => MonadState s (AspectT m)
deriving newtype instance MonadWriter w m => MonadWriter w (AspectT m)
deriving newtype instance MonadError e m => MonadError e (AspectT m)

makeAdvice ::
  forall ca m r.
    ( forall as.
      All ca as =>
      NP I as ->
      AspectT m (AspectT m r -> AspectT m r, NP I as)
    ) ->
    Advice ca m r
makeAdvice = Advice

makeArgsAdvice ::
  forall ca m r.
  Monad m =>
  -- | The function that tweaks the arguments.
  ( forall as.
    All ca as =>
    NP I as ->
    AspectT m (NP I as)
  ) ->
  Advice ca m r
makeArgsAdvice tweakArgs =
  makeAdvice $ \args -> do
    args' <- tweakArgs args
    pure (id, args')

