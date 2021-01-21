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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- |
-- This package provices the 'Advice' datatype, along for functions for creating,
-- manipulating, composing and applying values of that type.
--
-- 'Advice's represent generic transformations on 'DepT'-effectful functions of
-- any number of arguments.
module Control.Monad.Dep.Advice
  ( -- * The Advice type
    Advice,

    -- * Creating Advice values
    makeAdvice,
    makeArgsAdvice,
    makeExecutionAdvice,

    -- * Applying Advices
    advise,

    -- * Combining Advices by harmonizing their constraints
    -- $restrict
    restrictArgs,
    restrictEnv,
    restrictResult,

    -- * Constraint helpers
    Capable,
    EnvTop,
    EnvAnd,
    EnvEq,
    BaseConstraint,

    -- * "sop-core" re-exports
    -- $sop
    Top,
    All,
    And,
    NP (..),
    I (..),
    cfoldMap_NP,

    -- * "constraints" re-exports
    -- $constraints
    type (:-) (..),
    Dict (..),
  )
where

import Control.Monad.Dep
import Data.Constraint
import Data.Kind
import Data.SOP
import Data.SOP.Dict qualified as SOP
import Data.SOP.NP

{- $setup
 
>>> :set -XTypeApplications 
>>> import Control.Monad.Dep
>>> import Data.Constraint
>>> import Data.Kind
>>> import Data.SOP
>>> import Data.SOP.NP

-}


-- | A generic transformation of a 'DepT'-effectful function of any number of
-- arguments, provided the function satisfies certain constraints on the
-- arguments, the environment datatype and base monad, and the return type.
--
-- It is parameterized by three constraints:
--
-- * @ca@ of kind @Type -> Constraint@, the constraint required of each argument (usually something like @Show@).
-- * @cem@ of kind @Type -> (Type -> Type) -> Constraint@, the constraint required of the 'DepT'-environment / base monad combination (usually something like @HasLogger@).
-- * @cr@ of kind @Type -> Constraint@, the constraint required of the return type.
--
-- We can constrain the 'Advice' to work with concrete types by using partially
-- applied equality constraints in the case of @ca@ and @cr@, and 'EnvEq' in
-- the case of @cem@.
--
-- 'Advice's that don't care about a particular constraint can leave it
-- polymorphic, and this facilitates composition, but the constraint must be
-- given some concrete value ('Top' in the case of @ca@ and @cr@, 'EnvTop' in
-- the case of @cem@) through type application at the moment of applying the
-- 'Advice' with 'advise'.
type Advice ::
  (Type -> Constraint) ->
  (Type -> (Type -> Type) -> Constraint) ->
  (Type -> Constraint) ->
  Type
data Advice ca cem cr where
  Advice ::
    forall u ca cem cr.
    Proxy u ->
    ( forall as e m.
      (All ca as, Capable cem e m) =>
      NP I as ->
      DepT e m (u, NP I as)
    ) ->
    ( forall e m r.
      (Capable cem e m, cr r) =>
      u ->
      DepT e m r ->
      DepT e m r
    ) ->
    Advice ca cem cr

-- |
--    Aspects compose \"sequentially\" when tweaking the arguments, and
--    \"concentrically\" when tweaking the final 'DepT' action.
--
--    The first 'Advice' is the \"outer\" one. It tweaks the function arguments
--    first, and wraps around the execution of the second, \"inner\" 'Advice'.
instance Semigroup (Advice ca cem cr) where
  Advice outer tweakArgsOuter tweakExecutionOuter <> Advice inner tweakArgsInner tweakExecutionInner =
    let captureExistentials ::
          forall ca cem cr outer inner.
          Proxy outer ->
          ( forall as e m.
            (All ca as, Capable cem e m) =>
            NP I as ->
            DepT e m (outer, NP I as)
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
            DepT e m (inner, NP I as)
          ) ->
          ( forall e m r.
            (Capable cem e m, cr r) =>
            inner ->
            DepT e m r ->
            DepT e m r
          ) ->
          Advice ca cem cr
        captureExistentials _ tweakArgsOuter' tweakExecutionOuter' _ tweakArgsInner' tweakExecutionInner' =
          Advice
            (Proxy @(Pair outer inner))
            ( let tweakArgs ::
                    forall as e m.
                    (All ca as, Capable cem e m) =>
                    NP I as ->
                    DepT e m (Pair outer inner, NP I as)
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

-- |
--    The most general (and complex) way of constructing 'Advice's.
--
--    'Advice's work in two phases. First, the arguments of the transformed
--    function are collected into an n-ary product 'NP', and passed to the
--    first argument of 'makeAdvice', which produces a (possibly transformed)
--    product of arguments, along with some summary value of type @u@. Use @()@
--    as the summary value if you don't care about it.
--
--    In the second phase, the monadic action produced by the function once all
--    arguments have been given is transformed using the second argument of
--    'makeAdvice'. This second argument also receives the summary value of
--    type @u@ calculated earlier.
--
--    __/IMPORTANT!/__ When invoking this function, you must always give the type
--    of the existential @u@ through a type application. Otherwise you'll get
--    weird \"u is untouchable\" errors.
makeAdvice ::
  forall u ca cem cr.
  -- | The function that tweaks the arguments.
  ( forall as e m.
    (All ca as, Capable cem e m) =>
    NP I as ->
    DepT e m (u, NP I as)
  ) ->
  -- | The function that tweaks the execution.
  ( forall e m r.
    (Capable cem e m, cr r) =>
    u ->
    DepT e m r ->
    DepT e m r
  ) ->
  Advice ca cem cr
makeAdvice = Advice (Proxy @u)

-- |
--    Create an advice which only tweaks and/or analyzes the function arguments.
--
--    Notice that there's no @u@ parameter, unlike with 'makeAdvice'.
makeArgsAdvice ::
  forall ca cem cr.
  -- | The function that tweaks the arguments.
  ( forall as e m.
    (All ca as, Capable cem e m) =>
    NP I as ->
    DepT e m (NP I as)
  ) ->
  Advice ca cem cr
makeArgsAdvice tweakArgs =
  makeAdvice @()
    ( \args -> do
        args <- tweakArgs args
        pure ((), args)
    )
    (const id)

-- |
--    Create an advice which only tweaks the execution of the final monadic action.
--
--    Notice that there's no @u@ parameter, unlike with 'makeAdvice'.
makeExecutionAdvice ::
  forall ca cem cr.
  -- | The function that tweaks the execution.
  ( forall e m r.
    (Capable cem e m, cr r) =>
    DepT e m r ->
    DepT e m r
  ) ->
  Advice ca cem cr
makeExecutionAdvice tweakExecution = makeAdvice @() (\args -> pure (pure args)) (\() action -> tweakExecution action)

data Pair a b = Pair !a !b

--
--
--

-- | This helper type synonym has three parameters:
--
-- * A two-place typeclass relating a fully constructed environment type to the
-- monad on which the functions in the enviroment have their effects.
-- * The type constructor of an environment parameterizable by a monad.
-- * The monad to be used as the base monad for 'DepT'.
--
-- The result is a 'Constraint' that says that the environment parameterized by
-- 'DepT' over the base monad satisfies the first constraint, with 'DepT' over
-- the base monad as the effect type of the functions.
--
-- For example, if we have the constraint
--
-- @
--
--  type HasLogger :: Type -> (Type -> Type) -> Constraint
--  class HasLogger r m | r -> m where
--    logger :: r -> String -> m ()
-- @
--
-- and the parameterizable enviroment
--
-- @
-- type Env :: (Type -> Type) -> Type
-- data Env m = Env
--   { _logger :: String -> m (),
--     _repository :: Int -> m (),
--     _controller :: Int -> m String
--   }
-- instance HasLogger (Env m) m where
--   logger = _logger
-- @
--
-- then the constraint
--
-- @
-- Capable HasLogger Env IO
-- @
--
-- Means that the 'Env' parameterized by the 'DepT' transformer over 'IO'
-- contains a logging function that works in 'DepT' over 'IO'.
type Capable ::
  (Type -> (Type -> Type) -> Constraint) ->
  ((Type -> Type) -> Type) ->
  (Type -> Type) ->
  Constraint

type Capable c e m = (c (e (DepT e m)) (DepT e m), Monad m)

-- | Apply an 'Advice' to some compatible function. The function must have its
-- effects in 'DepT', and satisfy the constraints required by the 'Advice'.
--
-- __/IMPORTANT!/__ If the @ca@, @cem@ or @cr@ constraints of the supplied
-- 'Advice' remain polymorphic, they must be given types by means of type
-- applications.
advise ::
  forall ca cem cr as e m r advisee.
  (Multicurryable as e m r advisee, All ca as, Capable cem e m, cr r) =>
  -- | The advice to apply.
  Advice ca cem cr ->
  -- | A function to be adviced.
  advisee ->
  advisee
advise (Advice _ tweakArgs tweakExecution) advisee = do
  let uncurried = multiuncurry @as @e @m @r advisee
      uncurried' args = do
        (u, args') <- tweakArgs args
        tweakExecution u (uncurried args')
   in multicurry @as @e @m @r uncurried'

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
--    Useful as the @cem@ type application argument of 'advise' and 'restrictEnv'.
--
--    For similar behavior with the @ar@ and @cr@ type arguments of 'advise' and
--    'restrictEnv', use 'Top' from \"sop-core\".
type EnvTop :: (Type -> (Type -> Type) -> Constraint)
class EnvTop e m

instance EnvTop e m

-- |
--    Creates composite constraints on the environment and monad.
--
--    For example, an advice which requires both a @HasLogger@ and a
--    @HasRepository@ might use this.
--
--    Useful to build the @cem@ type application argument of 'advise' and
--    'restrictEnv'.
--
--    For similar behavior with the @ar@ and @cr@ type arguments of 'advise' and
--    'restrictEnv', use 'And' from \"sop-core\".
type EnvAnd :: (Type -> (Type -> Type) -> Constraint) -> (Type -> (Type -> Type) -> Constraint) -> (Type -> (Type -> Type) -> Constraint)
class (f e m, g e m) => (f `EnvAnd` g) e m

instance (f e m, g e m) => (f `EnvAnd` g) e m

infixl 7 `EnvAnd`

-- |
--    When whe don't want to advise functions in some generic 'DepT'
--    environment, but in a concrete environment with a concrete base monad,
--    having access to all the fields.
--
--    Useful to build the @cem@ type application argument of 'advise' and
--    'restricEnv'.
--
--    For similar behavior with the @ar@ and @cr@ type arguments of 'advise' and
--    'restrictEnv', use a partially applied type equality, like @((~) Int)@.
type EnvEq :: Type -> (Type -> Type) -> Type -> (Type -> Type) -> Constraint
class (c' ~ c, m' ~ m) => EnvEq c' m' c m

instance (c' ~ c, m' ~ m) => EnvEq c' m' c m

-- |
--    Allows us to require a constraint only on the base monad, for example a base moonad with @MonadIO@.
--
--    Useful to build @cem@ type application argument of 'advise' and 'restricEnv'.
type BaseConstraint :: ((Type -> Type) -> Constraint) -> (Type -> (Type -> Type) -> Constraint)
class c m => BaseConstraint c e m

instance c m => BaseConstraint c e m

-- $restrict
--
--    'Advice' values can be composed using the 'Monoid' instance, but only if
--    the have the same constraint parameters. It's unfortunate that—unlike with
--    normal functions—'Advice' constaints aren't automatically "collected"
--    during composition.
--
--    We need to harmonize the constraints on each value by turning them into the
--    combination of all constraints. The functions in this section help with
--    that.
--
--    These functions take as parameter evidence of entailment between
--    constraints, using the type '(:-)' from the \"constraints\" package.  But
--    how to construct such evidence? By using the 'Sub' and the 'Dict'
--    constructors, with either an explicit type signature:
--
-- @
-- returnMempty :: Advice ca cem Monoid
--
-- returnMempty' :: Advice ca cem (Monoid `And` Show)
-- returnMempty' = restrictResult (Sub Dict) returnMempty
-- @
--
-- or a type application to the restriction function:
--
-- @
-- returnMempty'' = restrictResult @(Monoid `And` Show) (Sub Dict) returnMempty
-- @
--
-- Another example:
--
-- @
-- doLogging :: Advice Show HasLogger cr
--
--
-- type HasLoggerAndWriter :: Type -> (Type -> Type) -> Constraint
-- type HasLoggerAndWriter = HasLogger \`EnvAnd\` BaseConstraint (MonadWriter TestTrace)
--
-- doLogging':: Advice Show HasLoggerAndWriter cr
-- doLogging'= restrictEnv (Sub Dict) doLogging
--
-- doLogging'' = restrictEnv @HasLoggerAndWriter (Sub Dict) doLogging
-- @

-- |
--    Makes the constraint on the arguments more restrictive.

-- think about the order of the type parameters... which is more useful? is it relevant?
-- A possible principle to follow:

-- * We are likely to know the "less" constraint, because advices are likely to compe pre-packaged and having a type signature.

-- * We arent' so sure about having a signature for a whole composed Advice, because the composition might be done

-- on the fly, while constructing a record, without a top-level binding with a type signature.
-- This seems to favor putting "more" first.
restrictArgs ::
  forall more less cem cr.
  -- | Evidence that one constraint implies the other.
  (forall r. more r :- less r) ->
  -- | Advice with less restrictive constraint on the args.
  Advice less cem cr ->
  -- | Advice with more restrictive constraint on the args.
  Advice more cem cr
restrictArgs evidence (Advice proxy tweakArgs tweakExecution) =
  let captureExistential ::
        forall more less cem cr u.
        (forall r. more r :- less r) ->
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
          ( let tweakArgs'' :: forall as e m. (All more as, Capable cem e m) => NP I as -> DepT e m (u, NP I as)
                tweakArgs'' = case SOP.mapAll @more @less (translateEvidence @more @less evidence') of
                  f -> case f (SOP.Dict @(All more) @as) of
                    SOP.Dict -> \args -> tweakArgs' @as @e @m args
             in tweakArgs''
          )
          tweakExecution'
   in captureExistential evidence proxy tweakArgs tweakExecution

-- |
--    Makes the constraint on the environment / monad more restrictive.
restrictEnv ::
  forall more ca less cr.
  -- | Evidence that one constraint implies the other.
  (forall e m. Capable more e m :- Capable less e m) ->
  -- | Advice with less restrictive constraint on the environment and base monad.
  Advice ca less cr ->
  -- | Advice with more restrictive constraint on the environment and base monad.
  Advice ca more cr
restrictEnv evidence (Advice proxy tweakArgs tweakExecution) =
  let captureExistential ::
        forall more ca less cr u.
        (forall e m. Capable more e m :- Capable less e m) ->
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
          ( let tweakArgs'' :: forall as e m. (All ca as, Capable more e m) => NP I as -> DepT e m (u, NP I as)
                tweakArgs'' = case evidence' @e @m of Sub Dict -> \args -> tweakArgs' @as @e @m args
             in tweakArgs''
          )
          ( let tweakExecution'' :: forall e m r. (Capable more e m, cr r) => u -> DepT e m r -> DepT e m r
                tweakExecution'' = case evidence' @e @m of Sub Dict -> \u action -> tweakExecution' @e @m @r u action
             in tweakExecution''
          )
   in captureExistential evidence proxy tweakArgs tweakExecution

-- |
--    Makes the constraint on the result more restrictive.
restrictResult ::
  forall more ca cem less.
  -- | Evidence that one constraint implies the other.
  (forall r. more r :- less r) ->
  -- | Advice with less restrictive constraint on the result.
  Advice ca cem less ->
  -- | Advice with more restrictive constraint on the result.
  Advice ca cem more
restrictResult evidence (Advice proxy tweakArgs tweakExecution) =
  let captureExistential ::
        forall more ca cem less u.
        (forall r. more r :- less r) ->
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
          ( let tweakExecution'' :: forall e m r. (Capable cem e m, more r) => u -> DepT e m r -> DepT e m r
                tweakExecution'' = case evidence' @r of Sub Dict -> \u action -> tweakExecution' @e @m @r u action
             in tweakExecution''
          )
   in captureExistential evidence proxy tweakArgs tweakExecution

translateEvidence :: forall more less a. (forall x. more x :- less x) -> SOP.Dict more a -> SOP.Dict less a
translateEvidence evidence SOP.Dict =
  case evidence @a of
    Sub Dict -> SOP.Dict @less @a

-- $sop
-- Some useful definitions re-exported the from \"sop-core\" package.
--
-- 'NP' is an n-ary product used to represent the argument lists of functions.
--
-- 'Top' is the \"always satisfied\" constraint, useful when whe don't want to require anything specific.
--
-- 'And' combines constraints.
--
-- 'All' says that some constraint is satisfied by all the types of an 'NP' product.
--
-- 'I' is an identity functor.
--
-- 'cfoldMap_NP' is useful to construct homogeneous lists out of the 'NP' product, for example
--
-- @
-- cfoldMap_NP (Proxy @Show) (\\(I a) -> [show a])
-- @

-- $constraints
--
-- Some useful definitions re-exported the from \"constraints\" package.
--
-- 'Dict' and '(:-)' are GADTs used to capture and transform constraints.
