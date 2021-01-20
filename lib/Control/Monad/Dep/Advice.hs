{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Control.Monad.Dep.Advice
  ( Advice (..),
    advise,
    Capable,
    EnvTop,
    EnvAnd,
    EnvEq,
    BaseConstraint,
    restrictArgs,
    restrictEnv,
    restrictResult,
    -- * "sop-core" re-exports
    Top,
    All,
    And,
    NP(..),
    I(..),
    cfoldMap_NP,
    -- * "constraints" re-export
    type (:-)(..),
    Dict(..)
  )
where

import Control.Monad.Dep
import Data.Constraint
import Data.Kind
import Data.SOP
import Data.SOP.NP
import Data.SOP.Dict qualified as SOP 

--
--
--
type Capable ::
  (Type -> (Type -> Type) -> Constraint) ->
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Constraint

type Capable c e m = (c (e (DepT e m)) (DepT e m), Monad m)

-- type Advice ::
--   (Type -> Constraint) ->
--   (Type -> (Type -> Type) -> Constraint) ->
--   ((Type -> Type) -> Type) ->
--   (Type -> Type) ->
--   Type
data Advice ca cem cr where
  Advice ::
    forall u ca cem cr.
    Proxy u ->
    ( forall as e m.
      (All ca as, Capable cem e m) =>
      NP I as ->
      DepT e m (u,NP I as)
    ) ->
    ( forall e m r.
      (Capable cem e m, cr r) =>
      u ->
      DepT e m r ->
      DepT e m r
    ) ->
    Advice ca cem cr

data Pair a b = Pair !a !b

-- |
--    The first advice is the "outer" one. It gets executed first on the way of
--    calling the advised function, and last on the way out of the function.

-- But what about the order of argument manipulation? I'm not sure...
instance Semigroup (Advice ca cem cr) where
  Advice outer tweakArgsOuter tweakExecutionOuter <> Advice inner tweakArgsInner tweakExecutionInner =
    let captureExistentials ::
          forall ca cem cr outer inner.
          Proxy outer ->
          ( forall as e m.
            (All ca as, Capable cem e m) =>
            NP I as ->
            DepT e m (outer,NP I as)
          ) ->
          ( forall e m r.
            (Capable cem e m, cr r) =>
            outer ->
            DepT e m r ->
            DepT e m r
          ) ->
          Proxy inner ->
          ( forall as e m.
            (All ca as, Capable cem e m) =>
            NP I as ->
            DepT e m (inner,NP I as)
          ) ->
          ( forall e m r.
            (Capable cem e m, cr r) =>
            inner ->
            DepT e m r ->
            DepT e m r
          ) ->
          Advice ca cem cr
        captureExistentials _ tweakArgsOuter' tweakExecutionOuter' _ tweakArgsInner' tweakExecutionInner' =
          Advice @(Pair outer inner) @ca @cem @cr
            (Proxy @(Pair outer inner))
            ( let tweakArgs ::
                    forall as e m.
                    (All ca as, Capable cem e m) =>
                    NP I as ->
                    DepT e m (Pair outer inner,NP I as)
                  tweakArgs args =
                    do
                      (uOuter, argsOuter) <- tweakArgsOuter' @as @e @m args
                      (uInner, argsInner) <- tweakArgsInner' @as @e @m argsOuter
                      pure (Pair uOuter uInner, argsInner)
               in tweakArgs
            )
            ( let tweakExecution ::
                    forall e m r.
                    (Capable cem e m, cr r) =>
                    Pair outer inner ->
                    DepT e m r ->
                    DepT e m r
                  tweakExecution =
                    ( \(Pair uOuter uInner) action ->
                        tweakExecutionOuter' @e @m @r uOuter (tweakExecutionInner' @e @m @r uInner action)
                    )
               in tweakExecution
            )
     in captureExistentials @ca @cem @cr outer tweakArgsOuter tweakExecutionOuter inner tweakArgsInner tweakExecutionInner

instance Monoid (Advice ca cem cr) where
  mappend = (<>)
  mempty = Advice (Proxy @()) (\args -> pure (pure args)) (const id)

advise ::
  forall ca cem cr as e m r advisee.
  (Multicurryable as e m r advisee, All ca as, Capable cem e m, cr r) =>
  Advice ca cem cr ->
  advisee ->
  advisee
advise (Advice _ tweakArgs tweakExecution) advisee = do
  let uncurried = multiuncurry @as @e @m @r advisee
      uncurried' args = do
        (u,args') <- tweakArgs args
        tweakExecution u (uncurried args')
   in multicurry @as @e @m @r uncurried'

-- this class is for decomposing I think. It should ignore all constraints.
-- do we need to include e and m here?
type Multicurryable ::
  [Type] ->
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Type ->
  Type ->
  Constraint
class Multicurryable as e m r curried | curried -> as e m r where
  multiuncurry :: curried -> NP I as -> DepT e m r
  multicurry :: (NP I as -> DepT e m r) -> curried

instance Multicurryable '[] e m r (DepT e m r) where
  multiuncurry action Nil = action
  multicurry f = f Nil

instance Multicurryable as e m r curried => Multicurryable (a ': as) e m r (a -> curried) where
  multiuncurry f (I a :* as) = multiuncurry @as @e @m @r @curried (f a) as
  multicurry f a = multicurry @as @e @m @r @curried (f . (:*) (I a))

-- |
--    A constraint which requires nothing of the environment and the associated monad.
--
--    Pass this with a type application to 'advise' and 'advise' when no constraint is needed.
--
--    The @-Top@ and @-And@ constraints have been lifted from the @Top@ and @And@ constraints from sop-core.
type EnvTop :: (Type -> (Type -> Type) -> Constraint)
class EnvTop e m

instance EnvTop e m

-- |
--    Creates composite constraints on the environment and monad.
--
--    For example, an advice which requires both a @HasLogger@ and a
--    @HasRepository@ migh use this.
type EnvAnd :: (Type -> (Type -> Type) -> Constraint) -> (Type -> (Type -> Type) -> Constraint) -> (Type -> (Type -> Type) -> Constraint)
class (f e m, g e m) => (f `EnvAnd` g) e m

instance (f e m, g e m) => (f `EnvAnd` g) e m

infixl 7 `EnvAnd`

-- |
--    Useful when whe don't want to instrument some generic environment, but a
--    concrete one, with direct access to all fields and all that.
type EnvEq :: Type -> (Type -> Type) -> Type -> (Type -> Type) -> Constraint
class (c' ~ c, m' ~ m) => EnvEq c' m' c m

instance (c' ~ c, m' ~ m) => EnvEq c' m' c m

-- |
--    Allows us to require a constraint only on the base monad. Useful for requiring @MonadIO@ for example.
type BaseConstraint :: ((Type -> Type) -> Constraint) -> (Type -> (Type -> Type) -> Constraint)
class c m => BaseConstraint c e m

instance c m => BaseConstraint c e m

-- think about the order of the type parameters... which is more useful? is it relevant?
-- A possible principle to follow: 
-- * We are likely to know the "less" constraint, because advices are likely to compe pre-packaged and having a type signature.
-- * We arent' so sure about having a signature for a whole composed Advice, because the composition might be done
-- on the fly, while constructing a record, without a top-level binding with a type signature.
-- This seems to favor putting "more" first.
restrictArgs :: forall more less cem cr. (forall r . more r :- less r) -> Advice less cem cr -> Advice more cem cr
restrictArgs evidence (Advice proxy tweakArgs tweakExecution) = 
    let captureExistential ::
          forall more less cem cr u.
          (forall r . more r :- less r) ->
          Proxy u ->
          ( forall as e m.
            (All less as, Capable cem e m) =>
            NP I as ->
            DepT e m (u, NP I as)
          ) ->
          ( forall e m r.
            (Capable cem e m, cr r) =>
            u ->
            DepT e m r ->
            DepT e m r
          ) ->
          Advice more cem cr
        captureExistential evidence' _ tweakArgs' tweakExecution' = 
            Advice 
            (Proxy @u) 
            (let tweakArgs'' :: forall as e m. (All more as, Capable cem e m) => NP I as -> DepT e m (u, NP I as)
                 tweakArgs'' = case SOP.mapAll @more @less (translateEvidence @more @less evidence') of
                       f -> case f (SOP.Dict @(All more) @as) of
                         SOP.Dict -> \args -> tweakArgs' @as @e @m args 
              in tweakArgs'')
            tweakExecution' 
     in captureExistential evidence proxy tweakArgs tweakExecution  
    
restrictEnv :: forall more less ca cr . (forall e m . Capable more e m :- Capable less e m) -> Advice ca less cr -> Advice ca more cr
restrictEnv evidence (Advice proxy tweakArgs tweakExecution) = 
    let captureExistential ::
          forall ca more less cr u.
          (forall e m . Capable more e m :- Capable less e m) -> 
          Proxy u ->
          ( forall as e m.
            (All ca as, Capable less e m) =>
            NP I as ->
            DepT e m (u, NP I as)
          ) ->
          ( forall e m r.
            (Capable less e m, cr r) =>
            u ->
            DepT e m r ->
            DepT e m r
          ) ->
          Advice ca more cr
        captureExistential evidence' _ tweakArgs' tweakExecution' = 
            Advice 
            (Proxy @u) 
             (let tweakArgs'' :: forall as e m. (All ca as, Capable more e m) => NP I as -> DepT e m (u, NP I as)
                  tweakArgs'' = case evidence' @e @m of Sub Dict -> \args -> tweakArgs' @as @e @m args
               in tweakArgs'')
            (let tweakExecution'' :: forall e m r. (Capable more e m, cr r) => u -> DepT e m r -> DepT e m r 
                 tweakExecution'' = case evidence' @e @m of Sub Dict -> \u action -> tweakExecution' @e @m @r u action
              in tweakExecution'') 
     in captureExistential evidence proxy tweakArgs tweakExecution  

restrictResult :: forall more less ca cem . (forall r . more r :- less r) -> Advice ca cem less -> Advice ca cem more
restrictResult evidence (Advice proxy tweakArgs tweakExecution) = 
    let captureExistential ::
          forall ca cem more less u.
          (forall r . more r :- less r) ->
          Proxy u ->
          ( forall as e m.
            (All ca as, Capable cem e m) =>
            NP I as ->
            DepT e m (u, NP I as)
          ) ->
          ( forall e m r.
            (Capable cem e m, less r) =>
            u ->
            DepT e m r ->
            DepT e m r
          ) ->
          Advice ca cem more
        captureExistential evidence' _ tweakArgs' tweakExecution' = 
            Advice 
            (Proxy @u) 
            tweakArgs' 
            (let tweakExecution'' :: forall e m r. (Capable cem e m, more r) => u -> DepT e m r -> DepT e m r 
                 tweakExecution'' = case evidence' @r of Sub Dict -> \u action -> tweakExecution' @e @m @r u action
              in tweakExecution'') 
     in captureExistential evidence proxy tweakArgs tweakExecution  
    
translateEvidence :: forall more less a. (forall x . more x :- less x) -> SOP.Dict more a -> SOP.Dict less a
translateEvidence evidence SOP.Dict = 
    case evidence @a of 
        Sub Dict -> SOP.Dict @less @a


