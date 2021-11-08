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
module Control.Monad.Dep.Advice
  ( 
    -- * The Advice type
    Advice,
    -- * Creating Advice values
    AspectT (..),
    makeAdvice,
    makeArgsAdvice,
    makeExecutionAdvice,
    -- * Preparing components for being advised
    advising,
    -- * Applying Advices
    advise,
    -- * Advising entire records
    -- $records
    adviseRecord,
    -- * Harmonizing Advice argument constraints
    -- $restrict
    restrictArgs,
    -- * DepT-specific helpers
    runFromEnv,
    runFromDep,
    popRecord',
    popRecord,
    popAdvice',
    popAdvice,
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
import Control.Monad.Trans.Reader (ReaderT (..), withReaderT)
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

--
-- arg restriction
restrictArgs ::
  forall more less m r.
  -- | Evidence that one constraint implies the other. Every @x@ that has a @more@ instance also has a @less@ instance.
  (forall x. Dict more x -> Dict less x) ->
  -- | Advice with less restrictive constraint on the args.
  Advice less m r ->
  -- | Advice with more restrictive constraint on the args.
  Advice more m r
-- about the order of the type parameters... which is more useful?
-- A possible principle to follow:
-- We are likely to know the "less" constraint, because advices are likely to
-- come pre-packaged and having a type signature.
-- We arent' so sure about having a signature for a whole composed Advice,
-- because the composition might be done
-- on the fly, while constructing a record, without a top-level binding with a
-- type signature.  This seems to favor putting "more" first.
restrictArgs evidence (Advice advice) = Advice \args ->
    let advice' :: forall as. All more as => NP I as -> AspectT m (AspectT m r -> AspectT m r, NP I as)
        advice' args' =
            case Data.SOP.Dict.mapAll @more @less evidence of
               f -> case f (Dict @(All more) @as) of
                        Dict -> advice args'
     in advice' args

class Multicurryable as (DepT e_ m) r curried => Multiflip as e_ m r curried | curried -> as e_ m r where
  type DownToBaseMonad as e_ m r curried :: Type
  _runFromEnv :: m (e_ (DepT e_ m)) -> (e_ (DepT e_ m) -> curried) -> DownToBaseMonad as e_ m r curried
  _askFinalDepT :: (e_ (DepT e_ m) -> m curried) -> curried


instance Monad m => Multiflip '[] e_ m r (AspectT (DepT e_ m) r) where
  type DownToBaseMonad '[] e_ m r (AspectT (DepT e_ m) r) = m r
  _runFromEnv producer extractor = do
    e <- producer
    runDepT (runAspectT (extractor e)) e
  _askFinalDepT f = do
    env <- ask
    r <- lift (lift (f env))
    r

instance (Functor m, Multiflip as e_ m r curried) => Multiflip (a ': as) e_ m r (a -> curried) where
  type DownToBaseMonad (a ': as) e_ m r (a -> curried) = a -> DownToBaseMonad as e_ m r curried
  _runFromEnv producer extractor a = _runFromEnv @as @e_ @m @r @curried producer (\f -> extractor f a)
  _askFinalDepT f = 
    let switcheroo action a = fmap ($ a) action
     in _askFinalDepT @as @e_ @m @r . flip (fmap switcheroo f)


askFinalDepT ::
  forall as e_ m r curried. 
  Multiflip as e_ m r curried =>
  (e_ (DepT e_ m) -> m curried) -> curried
askFinalDepT = _askFinalDepT @as @e_ @m @r


type DistributiveRecord :: ((Type -> Type) -> Type) -> (Type -> Type) -> ((Type -> Type) -> Type) -> Constraint
class DistributiveRecord e_ m record where
    _distribute :: (e_ (DepT e_ m) -> m (record (DepT e_ m))) -> record (DepT e_ m)

type DistributiveProduct :: ((Type -> Type) -> Type) -> (Type -> Type) -> (k -> Type) -> Constraint
class DistributiveProduct e_ m product where
    _distributeProduct :: (e_ (DepT e_ m) -> m (product k)) -> product k

instance
  ( G.Generic (advised (DepT e_ m)),
    G.Rep (advised (DepT e_ m)) ~ G.D1 x (G.C1 y advised_),
    DistributiveProduct e_ m advised_,
    Functor m
  ) =>
  DistributiveRecord e_ m advised
  where
  _distribute f =
    let advised_ = _distributeProduct @_ @e_ @m (fmap (fmap (G.unM1 . G.unM1 . G.from)) f)
     in G.to (G.M1 (G.M1 advised_))

instance
  ( DistributiveProduct e_ m advised_left,
    DistributiveProduct e_ m advised_right,
    Functor m
  ) =>
  DistributiveProduct e_ m (advised_left G.:*: advised_right)
  where
  _distributeProduct f  = 
      _distributeProduct @_ @e_ @m (fmap (fmap (\(l G.:*: _) -> l)) f) 
      G.:*: 
      _distributeProduct @_ @e_ @m (fmap (fmap (\(_ G.:*: r) -> r)) f) 

instance
  ( 
    Functor m, 
    Multiflip as e_ m r advised
  ) =>
  DistributiveProduct e_ m (G.S1 ( 'G.MetaSel msymbol su ss ds) (G.Rec0 advised))
  where
  _distributeProduct f = G.M1 . G.K1 $ askFinalDepT @as @e_ @m @r (fmap (fmap (G.unK1 . G.unM1))  f)


-- | Having a 'DepT' action that returns a record-of-functions with effects in
-- 'DepT' is the same as having the record itself, because we can obtain the initial
-- environment by 'ask'ing for it in each member function.
popRecord' 
    :: forall e_ m record . DistributiveRecord e_ m record => 
    -- | 'DepT' action that returns the component
    DepT e_ m (record (DepT e_ m)) ->
    -- | component whose methods get the environment by 'ask'ing.
    record (DepT e_ m)
popRecord' (DepT (ReaderT action)) = _distribute @e_ @m @record action

popAdvice' 
    :: forall ca e_ m r . Monad m => 
    DepT e_ m (Advice ca (DepT e_ m) r) ->
    Advice ca (DepT e_ m) r
popAdvice' (DepT (ReaderT f)) = Advice \args -> do
    env <- ask
    Advice f' <- lift $ lift $ f env
    f' args

-- popAdvice (pure . f)

-- | Given a constructor that returns a record-of-functions with effects in 'DepT',
-- produce a record in which the member functions 'ask' for the environment themselves.
--
-- You must have a sufficiently polymorphic constructor—both in the monad and
-- in the environment—to invoke this function.
--
-- 'component' lets you plug simple component constructors 
-- into a 'DepT'-based environment.
--
-- Compare with 'Control.Monad.Dep.Env.constructor' from "Control.Monad.Dep.Env", which 
-- is intended to be used with 'Control.Monad.Dep.Env.fixEnv'-based environments.
popRecord 
    :: forall e_ m record . (Applicative m, DistributiveRecord e_ m record) => 
    -- | constructor which takes the environment as a positional parameter.
    (e_ (DepT e_ m) -> record (DepT e_ m)) ->
    -- | component whose methods get the environment by 'ask'ing.
    record (DepT e_ m)
popRecord f = _distribute @e_ @m (pure . f)

popAdvice 
    :: forall ca e_ m r . Monad m => 
    (e_ (DepT e_ m) -> Advice ca (DepT e_ m) r) ->
    Advice ca (DepT e_ m) r
popAdvice f = popAdvice' (DepT (ReaderT (pure . f)))


runFromEnv ::
  forall as e_ m r curried.
  Multiflip as e_ m r curried =>
  -- | action that gets hold of the environment
  m (e_ (DepT e_ m)) ->
  -- | gets a function from the environment with effects in 'DepT'
  (e_ (DepT e_ m) -> curried) ->
  -- | a new function with effects in the base monad
  DownToBaseMonad as e_ m r curried
runFromEnv = _runFromEnv

-- | Like 'runFromEnv', but the function to run is extracted from a dependency
-- @dep@ which is found using 'Has'. The selector should be concrete enough to
-- identify @dep@ in the environment.
runFromDep ::
  forall dep as e_ m r curried.
  (Multiflip as e_ m r curried, Has dep (DepT e_ m) (e_ (DepT e_ m))) =>
  -- | action that gets hold of the environment
  m (e_ (DepT e_ m)) ->
  -- | selector that gets a function from a dependency found using 'Has'
  (dep (DepT e_ m) -> curried) ->
  -- | a new function with effects in the base monad
  DownToBaseMonad as e_ m r curried
runFromDep envAction member = _runFromEnv envAction (member . dep)

