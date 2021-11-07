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
    makeArgsAdvice,
    makeExecutionAdvice,
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

instance Monad m => Semigroup (Advice ca m r) where
  Advice outer <> Advice inner = Advice \args -> do
    (tweakOuter, argsOuter) <- outer args
    (tweakInner, argsInner) <- inner argsOuter
    pure (tweakOuter . tweakInner, argsInner)

instance Monad m => Monoid (Advice ca m r) where
  mappend = (<>)
  mempty = Advice \args -> pure (id, args)



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

advising 
    :: Coercible (r_ m) (r_ (AspectT m))
    => (r_ (AspectT m) -> r_ (AspectT m))
    -> r_ m -> r_ m
advising f = coerce . f . coerce

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

makeExecutionAdvice ::
  forall ca m r.
  Applicative m =>
  -- | The function that tweaks the execution.
  ( AspectT m r ->
    AspectT m r
  ) ->
  Advice ca m r
makeExecutionAdvice tweakExecution = makeAdvice \args -> pure (tweakExecution, args)

type Multicurryable ::
  [Type] ->
  (Type -> Type) ->
  Type ->
  Type ->
  Constraint
class Multicurryable as m r curried | curried -> as m r where
  multiuncurry :: curried -> NP I as -> AspectT m r
  multicurry :: (NP I as -> AspectT m r) -> curried

instance Monad m => Multicurryable '[] m r (AspectT m r) where
  multiuncurry action Nil = action
  multicurry f = f Nil

instance Multicurryable as m r curried => Multicurryable (a ': as) m r (a -> curried) where
  multiuncurry f (I a :* as) = multiuncurry @as @m @r @curried (f a) as
  multicurry f a = multicurry @as @m @r @curried (f . (:*) (I a))

advise ::
  forall ca m r as advisee.
  (Multicurryable as m r advisee, All ca as, Monad m) =>
  -- | The advice to apply.
  Advice ca m r ->
  -- | A function to be adviced.
  advisee ->
  advisee
advise (Advice f) advisee = do
  let uncurried = multiuncurry @as @m @r advisee
      uncurried' args = do
        (tweakExecution, args') <- f args
        tweakExecution (uncurried args')
   in multicurry @as @m @r uncurried'

-- | Gives 'Advice' to all the functions in a record-of-functions.
--
-- The function that builds the advice receives a list of tuples @(TypeRep, String)@
-- which represent the record types and fields names we have
-- traversed until arriving at the advised function. This info can be useful for
-- logging advices. It's a list instead of a single tuple because
-- 'adviseRecord' works recursively.
--
-- __/TYPE APPLICATION REQUIRED!/__ The @ca@ constraint on function arguments
-- and the @cr@ constraint on the result type must be supplied by means of a
-- type application. Supply 'Top' if no constraint is required.
adviseRecord ::
  forall ca cr m advised.
  AdvisedRecord ca m cr advised =>
  -- | The advice to apply.
  (forall r . cr r => [(TypeRep, String)] -> Advice ca m r) ->
  -- | The record to advise recursively.
  advised (AspectT m) ->
  -- | The advised record.
  advised (AspectT m)
adviseRecord = _adviseRecord @ca @m @cr []

type AdvisedRecord :: (Type -> Constraint) -> (Type -> Type) -> (Type -> Constraint) -> ((Type -> Type) -> Type) -> Constraint
class AdvisedRecord ca m cr advised where
  _adviseRecord :: [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca m r) -> advised (AspectT m) -> advised (AspectT m)

type AdvisedProduct :: (Type -> Constraint) -> (Type -> Type) -> (Type -> Constraint) -> (k -> Type) -> Constraint
class AdvisedProduct ca m cr advised_ where
  _adviseProduct :: TypeRep -> [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca m r) -> advised_ k -> advised_ k

instance
  ( G.Generic (advised (AspectT m)),
    -- G.Rep (advised (AspectT m)) ~ G.D1 ('G.MetaData name mod p nt) (G.C1 y advised_),
    G.Rep (advised (AspectT m)) ~ G.D1 x (G.C1 y advised_),
    Typeable advised,
    AdvisedProduct ca m cr advised_
  ) =>
  AdvisedRecord ca m cr advised
  where
  _adviseRecord acc f unadvised =
    let G.M1 (G.M1 unadvised_) = G.from unadvised
        advised_ = _adviseProduct @_ @ca @m @cr (typeRep (Proxy @advised)) acc f unadvised_
     in G.to (G.M1 (G.M1 advised_))

instance
  ( AdvisedProduct ca m cr advised_left,
    AdvisedProduct ca m cr advised_right
  ) =>
  AdvisedProduct ca m cr (advised_left G.:*: advised_right)
  where
  _adviseProduct tr acc f (unadvised_left G.:*: unadvised_right) = _adviseProduct @_ @ca @m @cr tr acc f unadvised_left G.:*: _adviseProduct @_ @ca @m @cr tr acc f unadvised_right

data RecordComponent
  = Terminal
  | IWrapped
  | Recurse

type DiscriminateAdvisedComponent :: Type -> RecordComponent
type family DiscriminateAdvisedComponent c where
  DiscriminateAdvisedComponent (a -> b) = Terminal
  DiscriminateAdvisedComponent (AspectT m x) = Terminal
  DiscriminateAdvisedComponent (Identity _) = IWrapped
  DiscriminateAdvisedComponent (I _) = IWrapped
  DiscriminateAdvisedComponent _ = Recurse

type AdvisedComponent :: RecordComponent -> (Type -> Constraint) -> (Type -> Type) -> (Type -> Constraint) -> Type -> Constraint
class AdvisedComponent component_type ca m cr advised where
  _adviseComponent :: [(TypeRep, String)] -> (forall r. cr r => [(TypeRep, String)] -> Advice ca m r) -> advised -> advised

instance
  ( AdvisedComponent (DiscriminateAdvisedComponent advised) ca m cr advised,
    KnownSymbol fieldName
  ) =>
  AdvisedProduct ca m cr (G.S1 ( 'G.MetaSel ( 'Just fieldName) su ss ds) (G.Rec0 advised))
  where
  _adviseProduct tr acc f (G.M1 (G.K1 advised)) =
    let acc' = acc ++ [(tr, symbolVal (Proxy @fieldName))]
     in G.M1 (G.K1 (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @m @cr acc' f advised))

instance
  AdvisedRecord ca m cr advisable =>
  AdvisedComponent Recurse ca m cr (advisable (AspectT m))
  where
  _adviseComponent acc f advised = _adviseRecord @ca @m @cr acc f advised

instance
  (Multicurryable as m r advised, All ca as, cr r, Monad m) =>
  AdvisedComponent Terminal ca m cr advised
  where
  _adviseComponent acc f advised = advise @ca @m (f acc) advised

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca m cr advised =>
  AdvisedComponent IWrapped ca m cr (Identity advised)
  where
  _adviseComponent acc f (Identity advised) = Identity (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @m @cr acc f advised)

instance
  AdvisedComponent (DiscriminateAdvisedComponent advised) ca m cr advised =>
  AdvisedComponent IWrapped ca m cr (I advised)
  where
  _adviseComponent acc f (I advised) = I (_adviseComponent @(DiscriminateAdvisedComponent advised) @ca @m @cr acc f advised)

