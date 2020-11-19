{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language MultiWayIf #-}
{-# language PatternSynonyms #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language KindSignatures #-}
{-# language OverloadedStrings #-}
{-# language StandaloneDeriving #-}

module Poly.Typecheck
  ( typecheckDeclaration
  ) where

import Control.Monad (when,replicateM)
import Debug.Trace (trace,traceM)
import Control.Applicative (liftA2)
import Data.Foldable (foldlM)
import Data.Sequence (Seq,pattern Empty, pattern (:<|), pattern (:|>))
import Data.Maybe (listToMaybe,fromMaybe,fromJust)
import Data.Word (Word64)
import Data.Int (Int64)
import Poly.Unchained (Scope(Global,Local),ScopedIdentifier(ScopedIdentifier),Identifier(Identifier),Kind)
import Data.Map (Map)
import Data.Text.Short (ShortText)
import qualified Data.Kind as Kind
import qualified Data.List as List
import qualified Data.Set as S
import qualified Poly.Flattened as E
import qualified Data.Sequence as Seq
import qualified Data.Text.Short as TS
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map

data CtxElem
  = CtxForall !Word64 !Kind           -- ^ alpha
  | CtxVar !Word64 !Type              -- ^ x : A
  | CtxJoinPoint !Word64 !Type        -- ^ join x (y : A)
  | CtxExists !Word64 !Kind           -- ^ alpha^, kind
  | CtxExistsSolved !Word64 !Type !Kind -- ^ alpha^ = tau, tau must be monotype
  | CtxMarker !Word64                 -- ^ |> alpha^
  deriving stock (Eq,Show)

data Status = Poly | Mono

-- | Types, indexed by their kind: Monotype or Polytype.
--   Only Polytypes can have foralls.
-- data Type :: Status -> Kind.Type where
--   -- TUnit   :: Type a                         -- ^ ()
--   TGlobal :: !Word64 -> Type a                 -- ^ 5, 42, etc.
--   TVar    :: !Word64 -> Type a                 -- ^ alpha
--   TExists :: !Word64 -> Type a                 -- ^ alpha^
--   TForall :: !Word64 -> Type Poly -> Type Poly -- ^ forall alpha. A
--   TArr    :: Type a -> Type a -> Type a     -- ^ A -> B

-- deriving stock instance Show (Type a)
-- deriving stock instance Eq (Type a)

data WithUuid a = WithUuid {-# UNPACK #-} !Word64 a
  deriving stock (Functor)

data TypecheckError
  = MalformedType Type
  | MalformedContext
  | KindMismatch
  | TypeConstantsNotEqual
  | UnsolvedExistentials
  | ExpectedArrowKind
  | ExpectedTupleKind
  | NonIntegerKind
  | ZeroTuplePatterns
  | MultipleTuplePatterns
  | NonTupleScrutinee
  | MismatchedTupleScrutineeSize
  | ShadowedTypeVariable !ShortText
  | UnknownGlobalIdentifier !ShortText
  | MismatchedTupleSizes !Int !Int
  | UnknownLocalTypeIdentifier !ShortText
  | UnknownGlobalTypeIdentifier !ShortText
  deriving stock (Show)

data Assertions
  = Assert
  | NoAssert

data TypecheckResult a
  = TypecheckFailure !TypecheckError
  | TypecheckSuccess
      !Word64 -- New UUID
      !a
  deriving stock (Functor)

data Result a = Success !a | Failure !TypecheckError

-- This is just like E.Term except that global and local
-- identifiers are split up, and global identifiers are annotated
-- with their types.
data Term
  = GlobalIdentifier !Identifier !Type
  | LocalIdentifier !Identifier
  | Lam !Identifier !Term
  | Let !Identifier !Term !Term
  | App !Term !Term
  | Integer !Int64
  | Tuple [Term]
  | Rec !Type [JoinPoint] !Term
  | Jump !Identifier !Term
  | Case !Term [Alternative]
  deriving (Show)

data JoinPoint = JoinPoint
  { name :: !Identifier
  , argument :: !Identifier
  , argumentType :: !Type
  , body :: !Term
  } deriving (Show)

data Alternative = Alternative
  { constructor :: !E.Constructor
  , bindings :: ![Identifier]
  , arm :: !Term
  } deriving (Show)

data Type
  = IdentT !ScopedIdentifier !Kind
  | AppT !Identifier !(Map Word64 Kind) !Type !Kind
    -- ^ Result kind is redundant but useful.
  | Arr !Type !Type
    -- ^ Representation of arrow is always boxed
  | TupleT [Type]
    -- ^ Kind is just tuple representation
  | Forall !E.KindedIdentifier !Type
  | Exists !Word64 !Kind
  deriving (Show,Eq)
  -- ^ Existenial for type checking. All of these are supposed to
  -- get solved during type checking.

-- Only fails with UnknownGlobalIdentifier
lookupGlobalTermTypes :: Map Word64 Type -> E.Term -> Either TypecheckError Term
lookupGlobalTermTypes m = go where
  go (E.Var E.ScopedIdentifier{scope,uuid,original}) = case scope of
    Local -> Right (LocalIdentifier Identifier{uuid,original})
    Global -> case Map.lookup uuid m of
      Just ty -> Right (GlobalIdentifier Identifier{uuid,original} ty)
      Nothing -> Left (UnknownGlobalIdentifier original)
  go (E.Lam v b) = fmap (Lam v) (go b)
  go (E.Let v e b) = liftA2 (Let v) (go e) (go b)
  go (E.App a b) = liftA2 App (go a) (go b)
  go (E.Integer i) = Right (Integer i)
  go (E.Tuple xs) = fmap Tuple (mapM (go) xs)
  go (E.Case e alts) = do
    e' <- go e
    alts' <- mapM goAlt alts
    pure (Case e' alts')
  go (E.Rec ty jpts e) = do
    ty' <- lookupGlobalTypeKinds builtinTypes ty
    jpts' <- mapM goJoinPoint jpts
    e' <- go e
    pure (Rec ty' jpts' e')
  go (E.Jump name e) = do
    e' <- go e
    pure (Jump name e')
  goJoinPoint :: E.JoinPoint -> Either TypecheckError JoinPoint
  goJoinPoint E.JoinPoint{name,argument,argumentType,body} = do
    body' <- go body
    argumentType' <- lookupGlobalTypeKinds builtinTypes argumentType
    pure JoinPoint{name,argument,argumentType=argumentType',body=body'}
  goAlt :: E.Alternative -> Either TypecheckError Alternative
  goAlt E.Alternative{constructor,bindings,arm} = do
    arm' <- go arm
    pure (Alternative{constructor,bindings,arm=arm'})

lookupGlobalTypeKinds :: Map Word64 E.Kind -> E.Type -> Either TypecheckError Type
lookupGlobalTypeKinds !globals = go Map.empty where
  go !env (E.IdentT v@ScopedIdentifier{original,uuid,scope}) = case scope of
    Local -> maybe
      (Left (UnknownLocalTypeIdentifier original))
      (\k -> pure (IdentT v k))
      (Map.lookup uuid env)
    Global -> maybe
      (Left (UnknownGlobalTypeIdentifier original))
      (\k -> pure (IdentT v k))
      (Map.lookup uuid globals)
  go !env E.AppT{} = error "lookupGlobalTypeKinds: write this part"
  go !env (E.Arr a b) = liftA2 Arr (go env a) (go env b)
  go !env (E.TupleT xs) = fmap TupleT (mapM (go env) xs)
  go !env (E.Forall v@E.KindedIdentifier{original,uuid,kind} body) = do
    env' <- addResolution original uuid kind env
    body' <- go env' body
    pure (Forall v body')
    
addResolution ::
     ShortText -- just for error reporting
  -> Word64
  -> Kind
  -> Map Word64 Kind
  -> Either TypecheckError (Map Word64 Kind)
addResolution !original !uuid !kind !identifiers = Map.alterF
  (\x -> case x of
    Nothing -> pure $! Just $! kind
    Just _ -> Left $! ShadowedTypeVariable original
  ) uuid identifiers

-- newtype Globals = Globals
--   { terms :: !(Map Word64 (Type 'Poly))
--   }

-- | Parameters are:
--
-- * A UUID, state-like
-- * A boolean, reader-like
newtype Typecheck a = Typecheck { runTypecheck :: Word64 -> Assertions -> TypecheckResult a }
  deriving stock (Functor)

instance Applicative Typecheck where
  pure a = Typecheck (\w s -> TypecheckSuccess w a)
  Typecheck f <*> Typecheck a = Typecheck $ \w0 s -> case f w0 s of
    TypecheckFailure e -> TypecheckFailure e
    TypecheckSuccess w1 h -> case a w1 s of
      TypecheckFailure e -> TypecheckFailure e
      TypecheckSuccess w2 b -> TypecheckSuccess w2 (h b)

instance Monad Typecheck where
  Typecheck a >>= f = Typecheck $ \w0 s -> case a w0 s of
    TypecheckFailure e -> TypecheckFailure e
    TypecheckSuccess w1 b -> runTypecheck (f b) w1 s

run :: Typecheck a -> Either TypecheckError a
run (Typecheck f) = case f 40000 Assert of
  TypecheckSuccess _ a -> Right a
  TypecheckFailure e -> Left e

-- TODO: Check kinds of type constructors
typecheckDeclaration ::
     E.TermDeclaration
  -> Either TypecheckError ()
typecheckDeclaration E.TermDeclaration{name,type_=t0,definition,exported} = do
  let E.TypeScheme{representations,type_} = t0
  defn <- lookupGlobalTermTypes builtinTerms definition
  enrichedType <- lookupGlobalTypeKinds builtinTypes type_
  run $ do
    outputCtx <- typecheck Empty defn enrichedType
    case hasUnsolved outputCtx of
      False -> pure ()
      True -> failWith UnsolvedExistentials

-- | Type checking:
--   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ
typecheck ::
     Seq CtxElem
  -> Term
  -> Type
  -> Typecheck (Seq CtxElem)
typecheck !gamma expr typ = assertWellFormedType gamma typ $ case (expr, typ) of
  -- TODO: reinstate original Unit type checking
  -- -- 1I
  -- (EUnit, TUnit) -> return gamma
  -- 1I
  (Integer{}, IdentT ScopedIdentifier{uuid=1000,scope=Global} _) -> return gamma
  -- 1I^α, no-inference rule from section 8 of paper
  (Integer{}, Exists alpha alphaKind) -> case alphaKind of
    E.IntK -> solve gamma alpha alphaKind intType
    _ -> failWith NonIntegerKind
  -- → I^α, no-inference rule from section 8 of paper
  (Lam (E.Identifier{uuid=x}) e, Exists alpha alphaKind) -> case alphaKind of
    E.ArrowK k1 k2 -> do
      alpha1 <- freshTVar
      alpha2 <- freshTVar
      dropCtxVar x <$> typecheck
        (insertAt
          gamma 
          (CtxExists alpha alphaKind)
          (Seq.fromList
            [ CtxExists alpha2 k2
            , CtxExists alpha1 k1
            , CtxExistsSolved alpha
                ( Arr (Exists alpha1 k1)
                      (Exists alpha2 k2)
                ) (E.ArrowK k1 k2)
            ]
          ) :|> CtxVar x (Exists alpha1 k1)
        ) e (Exists alpha2 k2)
    _ -> failWith ExpectedArrowKind
  -- Tuple anologue of → I^α. Hopefully I got this right, but I have
  -- not confirmed it.
  (Tuple es, Exists alpha alphaKind) -> case alphaKind of
    E.TupleK ks -> do
      let esLen = length es
      let ksLen = length ks
      when (esLen /= ksLen) (failWith (MismatchedTupleSizes esLen ksLen))
      elemTyVars <- replicateM ksLen freshTVar
      let existsTys = zipWith Exists elemTyVars ks
      let ctxExistsTys = zipWith CtxExists elemTyVars ks
      let ctx0 = insertAt
            gamma 
            (CtxExists alpha alphaKind)
            (Seq.fromList ctxExistsTys
             :|> 
             CtxExistsSolved alpha
               ( TupleT existsTys
               ) alphaKind
            )
      -- TODO: Does any part of the context need to be dropped after
      -- doing this? I don't think so, but I'm not totally sure.
      foldlM
        (\ctx (e,t) -> typecheck ctx e t
        ) ctx0 (zip es existsTys)
    _ -> failWith ExpectedTupleKind
  -- Tuple pattern matching
  (Case e alts, _) -> case alts of
    [] -> failWith ZeroTuplePatterns
    Alternative{constructor=E.TupleConstructor,bindings,arm} : [] -> do
      -- Typesynth might not be right here, but we have no way to
      -- conjure up an expected kind for typecheck. If we did not have
      -- rep kinds, I don't think we would have this problem.
      (ety,gamma') <- typesynth gamma e
      let len = length bindings
      case ety of
        TupleT tys
          | length tys /= len -> failWith MismatchedTupleScrutineeSize
          | otherwise -> do
              let ctxs = zipWith (\Identifier{uuid} ty -> CtxVar uuid ty) bindings tys
              case bindings of
                [] -> error "empty tuple pattern not allowed"
                Identifier{uuid=uuid0} : _ -> do
                  dropCtxVar uuid0 <$> typecheck (gamma' <> Seq.fromList ctxs) arm typ
        _ -> failWith NonTupleScrutinee
    Alternative{constructor=E.TupleConstructor} : _ : _ -> failWith MultipleTuplePatterns
    -- Only works for nullary constructors, but that's a start.
    Alternative{constructor=E.CustomConstructor (E.Identifier{uuid=c0}),bindings=[]} : _ ->
      case Map.lookup c0 builtinNullaryConstructors of
        Nothing -> error "Sorry, only nullary constructors and tuples are allowed"
        Just ty -> do
          gamma0 <- typecheck gamma e ty
          foldlM
            ( \gamma1 (Alternative{constructor,bindings,arm}) -> case constructor of
              E.CustomConstructor (E.Identifier{uuid})
                | [] <- bindings -> typecheck gamma1 arm typ
                | otherwise -> error "binding must be empty in all patterns"
              _ -> error "cannot mix tuple constructors with user-defined data constructors"
            ) gamma0 alts
  -- ForallI
  (e, Forall E.KindedIdentifier{original,uuid=alpha,kind=alphaKind} a) -> do
    -- Do alpha conversion to avoid clashes
    alpha' <- freshTVar
    let alphaTy' = IdentT ScopedIdentifier{scope=Local,uuid=alpha',original} alphaKind
    dropCtxForall alpha' <$>
      typecheck (gamma :|> CtxForall alpha' alphaKind) e (typeSubst alphaTy' alpha a)
  -- ->I
  (Lam (E.Identifier{uuid=x}) e, Arr a b) -> do
    dropMarker (CtxVar x a) <$>
      typecheck (gamma :|> CtxVar x a) e b
  -- A jump can return any type, so we can ignore the type we are
  -- checking against.
  (Jump (E.Identifier{uuid=x}) e, _) -> do
    let argTy = lookupJoinPointArgType gamma x
    typecheck gamma e argTy
  -- Anologue of ->I for tuples, probably not actually needed, actually
  -- it might be needed.
  (Tuple es, TupleT ts) -> do
    let esLen = length es
    let tsLen = length ts
    when (esLen /= tsLen) (failWith (MismatchedTupleSizes esLen tsLen))
    foldlM
      (\ctx (e,t) -> typecheck ctx e t
      ) gamma (zip es ts)
  -- Sub
  (e, b) -> do
    (a, theta) <- typesynth gamma e
    subtype theta (apply theta a) (apply theta b)

-- | Type synthesising:
--   typesynth Γ e = (A, Δ) <=> Γ |- e => A -| Δ
typesynth :: Seq CtxElem -> Term -> Typecheck (Type, Seq CtxElem)
typesynth gamma expr = assertWellFormed gamma $ case expr of
  -- Var
  -- Should we use error here? I'm not sure. I think that after
  -- renaming, it should be guaranteed that the variable is found.
  LocalIdentifier E.Identifier{original,uuid} -> return
    ( fromMaybe (error $ "typesynth: not in scope " ++ TS.unpack original)
                (findVarType gamma uuid)
    , gamma
    )
  GlobalIdentifier _ ty -> return (ty,gamma)
  -- TODO: reinstate Anno
  -- -- Anno
  -- EAnno e a -> do
  --   delta <- typecheck gamma e a
  --   return (a, delta)
  -- 1I=>, removed for no-inference checking rule
  -- Integer{} -> return (typeInt, gamma)
  -- ->I=> Original rule, removed for the no-inference rule
  -- Lam (E.Identifier{uuid=x}) e -> do
  --   x'    <- freshVar
  --   alpha <- freshTVar
  --   beta  <- freshTVar
  --   delta <- dropMarker (CtxVar x' (Exists alpha)) <$>
  --     typecheck (gamma <> Seq.fromList
  --                          [ CtxExists alpha
  --                          , CtxExists beta
  --                          , CtxVar x' (Exists alpha)
  --                          ])
  --               (subst x' x e)
  --               (Exists beta)
  --   return (Arr (Exists alpha) (Exists beta), delta)
  -- ->E
  App e1 e2 -> do
    (a, theta) <- typesynth gamma e1
    typeapplysynth theta (apply theta a) e2
  Let Identifier{uuid=x} body e -> do
    (bty,gamma') <- typesynth gamma body
    (ety,gamma'') <- typesynth (gamma' :|> CtxVar x (apply gamma' bty)) e
    let gamma''' = dropCtxVar x gamma''
    pure (ety,gamma''')
  Rec retTy jpts body -> do
    let !jptUuid0 = case jpts of
          [] -> error "zero join points not supported"
          JoinPoint{name=Identifier{uuid}} : _ -> uuid
    -- First, dump all of the join points into the context.
    let gamma' = F.foldl'
          ( \g JoinPoint{argumentType,name=Identifier{uuid}} ->
            g :|> CtxJoinPoint uuid argumentType
          ) gamma jpts
    -- Now, typecheck them one by one.
    gamma'' <- foldlM
      ( \g JoinPoint{body,argumentType,argument=Identifier{uuid}} -> do
        let g' = g :|> CtxVar uuid argumentType
        g'' <- typecheck g' body retTy
        pure $ dropCtxVar uuid g''
      ) gamma' jpts
    gamma''' <- typecheck gamma'' body retTy
    pure (retTy, dropJoinPoint jptUuid0 gamma''')
  Tuple ts -> do
    -- No need for context application because none of the
    -- premises refer to types.
    (ts',gamma') <- mapAccumM typesynth gamma (trace "typesynth on tuple" ts)
    pure (TupleT ts', gamma')
  _ -> error ("typesynth could not handle:\n" ++ show gamma ++ "\n" ++ show expr)

-- | Type application synthesising
--   typeapplysynth Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ
typeapplysynth ::
     Seq CtxElem
  -> Type
  -> Term
  -> Typecheck (Type, Seq CtxElem)
typeapplysynth gamma typ e = assertWellFormedType gamma typ $ case typ of
  -- ForallApp
  Forall E.KindedIdentifier{uuid=alpha,kind=alphaKind} a -> do
    -- Do alpha conversion to avoid clashes
    alpha' <- freshTVar
    typeapplysynth (gamma :|> CtxExists alpha' alphaKind)
                   (typeSubst (Exists alpha' alphaKind) alpha a)
                   e
  -- alpha^App
  Exists alpha alphaKind -> case trace "typeapplysynth alpha^App" alphaKind of
    E.ArrowK k1 k2 -> do
      alpha1 <- freshTVar
      alpha2 <- freshTVar
      delta <- typecheck
        (insertAt
          gamma
          (CtxExists alpha alphaKind)
          ( Seq.fromList
            [ CtxExists alpha2 k2
            , CtxExists alpha1 k1
            , CtxExistsSolved alpha
                (Arr (Exists alpha1 k1) (Exists alpha2 k2))
                alphaKind
            ]
          )
        )
        e
        (Exists alpha1 k1)
      return (Exists alpha2 k2, delta)
    _ -> failWith ExpectedArrowKind
  -- ->App
  Arr a c -> do
    traceM "typeapplysynth ->App"
    delta <- typecheck gamma e a
    return (c, delta)

  _ -> error $ "typeapplysynth: don't know what to do with: TODO write this"

-- | Well-formedness of contexts
--   wf Γ <=> Γ ctx
wf :: Seq CtxElem -> Bool
wf gamma = case gamma of
  gamma' :|> c -> wf gamma' && case c of
    -- UvarCtx
    CtxForall alpha _ -> alpha `notElem` foralls gamma'
    -- VarCtx
    CtxVar x a -> x `notElem` vars gamma' && typewf gamma' a
    -- EvarCtx
    CtxExists alpha _ -> alpha `notElem` existentials gamma'
    -- SolvedEvarCtx
    CtxExistsSolved alpha tau _ -> alpha `notElem` existentials gamma'
                            && typewf gamma' tau
    -- MarkerCtx
    CtxMarker alpha -> alpha `notElem` markers gamma'
                  && alpha `notElem` existentials gamma'
    -- JoinPointCtx
    CtxJoinPoint x a -> x `notElem` vars gamma' && typewf gamma' a
  -- EmptyCtx
  _ -> True

-- | Well-formedness of types
--   typewf Γ A <=> Γ |- A
typewf :: Seq CtxElem -> Type -> Bool
typewf gamma typ = case typ of
  -- UvarWF
  IdentT ScopedIdentifier{uuid=alpha,scope=Local} _ -> alpha `elem` foralls gamma
  -- UnitWF
  -- TODO: Maybe confirm that the uuid is valid. But that should already
  -- be certain, and we do not have access to the necessary environment here.
  IdentT ScopedIdentifier{scope=Global} _ -> True
  -- ArrowWF
  Arr a b -> typewf gamma a && typewf gamma b
  -- ForallWF
  Forall E.KindedIdentifier{uuid=alpha,kind=alphaKind} a ->
    typewf (gamma :|> CtxForall alpha alphaKind) a
  -- EvarWF and SolvedEvarWF
  Exists alpha _ -> alpha `elem` existentials gamma
  TupleT xs -> all (typewf gamma) xs

-- Assert-like functionality to make sure that contexts and types are
-- well-formed
assertWellFormed :: Seq CtxElem -> Typecheck x -> Typecheck x
assertWellFormed gamma x = getAssertions >>= \case
  Assert | not (wf gamma) -> failWith MalformedContext
  _ -> x

assertWellFormedType :: Seq CtxElem -> Type -> Typecheck x -> Typecheck x
assertWellFormedType gamma a x = getAssertions >>= \case
  Assert
    | not (wf gamma) -> failWith MalformedContext
    | not (typewf gamma a) -> failWith (MalformedType a)
  _ -> x 

failWith :: TypecheckError -> Typecheck a
failWith e = Typecheck (\ !_ !_ -> TypecheckFailure e)

getAssertions :: Typecheck Assertions
getAssertions = Typecheck (\ !w !a -> TypecheckSuccess w a)

existentials :: Seq CtxElem -> [Word64]
existentials gamma = aux =<< gamma' where
  aux (CtxExists alpha _) = [alpha]
  aux (CtxExistsSolved alpha _ _) = [alpha]
  aux _ = []
  gamma' = F.toList gamma

foralls :: Seq CtxElem -> [Word64]
foralls gamma = [alpha | CtxForall alpha _ <- gamma']
  where
  gamma' = F.toList gamma

markers :: Seq CtxElem -> [Word64]
markers gamma = [alpha | CtxMarker alpha <- gamma']
  where
  gamma' = F.toList gamma

vars :: Seq CtxElem -> [Word64]
vars gamma = [x | CtxVar x _ <- gamma']
  where
  gamma' = F.toList gamma

-- | apply Γ A = [Γ]A
apply :: Seq CtxElem -> Type -> Type
apply gamma typ = case typ of
  IdentT v k -> IdentT v k
  Forall v t -> Forall v (apply gamma t)
  Exists v k -> maybe (Exists v k) (apply gamma) $ findSolved gamma v
  Arr t1 t2  -> Arr (apply gamma t1) (apply gamma t2)
  TupleT xs -> TupleT (map (apply gamma) xs)

-- | findSolved (ΓL,α^ = τ,ΓR) α = Just τ
-- Returns a monotype.
findSolved :: Seq CtxElem -> Word64 -> Maybe Type
findSolved gamma v = listToMaybe [t | CtxExistsSolved v' t _ <- gamma', v == v']
  where
  gamma' = F.toList gamma

lookupJoinPointArgType :: Seq CtxElem -> Word64 -> Type
lookupJoinPointArgType gamma v =
  case listToMaybe [t | CtxJoinPoint v' t <- gamma', v == v'] of
    Just r -> r
    Nothing -> error "lookupJoinPointArgType: could not find join point"
  where
  gamma' = F.toList gamma

-- | Does the context have any unsolved existentials?
hasUnsolved :: Seq CtxElem -> Bool
hasUnsolved gamma = not (List.null [() | CtxExists{} <- gamma'])
  where
  gamma' = F.toList gamma

-- | insertAt (ΓL,c,ΓR) c Θ = ΓL,Θ,ΓR
insertAt :: Seq CtxElem -> CtxElem -> Seq CtxElem -> Seq CtxElem
insertAt gamma c theta = gammaL <> theta <> gammaR
  where (gammaL, gammaR) = breakMarker c gamma

-- TODO: Fail with a proper error message. It is not clear to me
-- whether or not failure indicates a mistake in the typechecker.
breakMarker :: CtxElem -> Seq CtxElem -> (Seq CtxElem, Seq CtxElem)
breakMarker m xs = case seqSplit m xs of
  Nothing -> error "breakMarker: expected element to exist"
  Just (l,r) -> (l,r)

-- Expects exactly one occurence of the element.
seqSplit :: Eq a => a -> Seq a -> Maybe (Seq a, Seq a) 
seqSplit e s = case Seq.elemIndexL e s of
  Nothing -> Nothing
  Just i -> case Seq.splitAt i s of
    (a,b) -> case b of
      _ :<| b' -> Just (a,b')
      _ -> error "seqSplit is broken"

-- Expects exactly one occurence of the element.
seqSplitOn :: (a -> Bool) -> Seq a -> Maybe (Seq a, Seq a) 
seqSplitOn p s = case Seq.findIndexL p s of
  Nothing -> Nothing
  Just i -> case Seq.splitAt i s of
    (a,b) -> case b of
      _ :<| b' -> Just (a,b')
      _ -> error "seqSplit is broken"

freshTVar :: Typecheck Word64
freshTVar = Typecheck
  (\w _ -> TypecheckSuccess (w + 1) w)

freshVar :: Typecheck Word64
freshVar = freshTVar

-- | typeSubst A α B = [A/α]B
typeSubst :: Type -> Word64 -> Type -> Type
typeSubst t' v typ = case typ of
  IdentT ScopedIdentifier{uuid,scope} _ -> case scope of
    Global -> typ
    Local -> if uuid == v then t' else typ
  Forall v'@E.KindedIdentifier{uuid} t
    | uuid == v   -> Forall v' t
    | otherwise -> Forall v' (typeSubst t' v t)
  Exists v' k'
    | v' == v   -> t'
    | otherwise -> Exists v' k'
  Arr t1 t2 -> Arr (typeSubst t' v t1) (typeSubst t' v t2)
  TupleT ts -> TupleT (map (typeSubst t' v) ts)
  _ -> error ("typeSubst: missing case to handle: " ++ show typ)

-- | subst e' x e = [e'/x]e
-- subst :: Word64 -> Word64 -> Term -> Term
-- subst !e' !x = go
--   where
--   go expr = case expr of
--     GlobalIdentifier{} -> expr
--     LocalIdentifier v@E.Identifier{original,uuid}
--       | uuid == x -> LocalIdentifier E.Identifier{original,uuid=e'}
--       | otherwise -> LocalIdentifier v
--     Integer i -> Integer i
--     Lam x' e -> Lam x' (subst e' x e)
--     -- TODO: remove the equality test for replacement under lambda.
--     -- This cannot ever be equal.
--     -- E.Lam x' e | x' == x   -> E.Lam x' e
--     --            | otherwise -> E.Lam x' (subst e' x e)
--     App e1 e2 -> App (subst e' x e1) (subst e' x e2)
--     Tuple ts -> Tuple (map (subst e' x) ts)
--     Case e alts -> Case
--       (subst e' x e)
--       (map goAlt alts)
--     -- TODO: reinstate anno
--     -- EAnno e t             -> EAnno (subst e' x e) t
--   goAlt (Alternative{constructor,bindings,arm}) = Alternative
--     { constructor
--     , bindings
--     , arm = go arm
--     }

-- Drops the marker and everything after it.
dropMarker :: CtxElem -> Seq CtxElem -> Seq CtxElem
dropMarker m gamma = case seqSplit m gamma of
  Nothing -> error "dropMarker: did not encounter marker"
  Just (pre,_) -> pre

-- Drops the join point and everything after it.
dropJoinPoint :: Word64 -> Seq CtxElem -> Seq CtxElem
dropJoinPoint !w gamma =
  case seqSplitOn (\case {CtxJoinPoint v _ -> v == w; _ -> False}) gamma of
    Nothing -> error "dropCtxMarker: did not encounter marker"
    Just (pre,_) -> pre

-- Drops the marker and everything after it.
dropCtxMarker :: Word64 -> Seq CtxElem -> Seq CtxElem
dropCtxMarker !w gamma =
  case seqSplitOn (\case {CtxMarker v -> v == w; _ -> False}) gamma of
    Nothing -> error "dropCtxMarker: did not encounter marker"
    Just (pre,_) -> pre

-- Drops the marker and everything after it.
dropCtxForall :: Word64 -> Seq CtxElem -> Seq CtxElem
dropCtxForall !w gamma =
  case seqSplitOn (\case {CtxForall v _ -> v == w; _ -> False}) gamma of
    Nothing -> error "dropCtxForall: did not encounter variable"
    Just (pre,_) -> pre

-- Drops the annotated variable and everything after it.
dropCtxVar :: Word64 -> Seq CtxElem -> Seq CtxElem
dropCtxVar !w gamma =
  case seqSplitOn (\case {CtxVar v _ -> v == w; _ -> False}) gamma of
    Nothing -> error "dropCtxVar: did not encounter variable"
    Just (pre,_) -> pre

-- Drops unsolved existential and everything after it.
dropCtxExists :: Word64 -> Seq CtxElem -> Seq CtxElem
dropCtxExists !w gamma =
  case seqSplitOn (\case {CtxExists v _ -> v == w; _ -> False}) gamma of
    Nothing -> error "dropCtxExists: did not encounter marker"
    Just (pre,_) -> pre

splitCtxExists :: Word64 -> Seq CtxElem -> (Seq CtxElem, Seq CtxElem)
splitCtxExists !w gamma =
  case seqSplitOn (\case {CtxExists v _ -> v == w; _ -> False}) gamma of
    Nothing -> error "dropCtxExists: did not encounter marker"
    Just (pre,post) -> (pre,post)

typeInt :: Type
typeInt = IdentT ScopedIdentifier{uuid=1000,scope=Global,original="Int"} E.IntK

-- typeInt :: E.Type a
-- typeInt = IdentT E.ScopedIdentifier
--   { original = "Builtin.Int"
--   , uuid = 1000
--   , scope = Global
--   }

-- | findVarType (ΓL,x : A,ΓR) x = Just A
findVarType :: Seq CtxElem -> Word64 -> Maybe Type
findVarType gamma !v = listToMaybe [t | CtxVar v' t <- gamma', v == v']
  where
  gamma' = F.toList gamma

-- | Algorithmic subtyping:
--   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
subtype :: Seq CtxElem -> Type -> Type -> Typecheck (Seq CtxElem)
subtype gamma typ1 typ2 = assertWellFormedType gamma typ1 $ assertWellFormedType gamma typ2 $
  case (typ1, typ2) of
    -- <:Var
    -- Note: We ignore the kinds. I think this is fine since if the
    -- type is the same, the kinds are going to match. 
    (IdentT ScopedIdentifier{uuid=alpha,scope=Local} _, IdentT ScopedIdentifier{uuid=alpha',scope=Local} _) | alpha == alpha' -> return gamma
    -- <:Unit
    (IdentT ScopedIdentifier{uuid=x,scope=Global} _, IdentT ScopedIdentifier{uuid=y,scope=Global} _) -> if x == y
      then return gamma
      else failWith TypeConstantsNotEqual
    -- <:Exvar
    (Exists alpha _, Exists alpha' _)
      | alpha == alpha' && alpha `elem` existentials gamma -> return gamma
    -- <:->
    (Arr a1 a2, Arr b1 b2) -> do
      theta <- subtype gamma b1 a1
      subtype theta (apply theta a2) (apply theta b2)

    -- Tuples, similar to arrow but covariant in everything.
    (TupleT as1, TupleT as2) -> do
      let len1 = length as1
      let len2 = length as2
      when (len1 /= len2) (failWith (MismatchedTupleSizes len1 len2))
      -- TODO: context application on head is not needed
      foldlM
        (\ctx (a1,a2) -> subtype ctx (apply ctx a1) (apply ctx a2)
        ) gamma (zip as1 as2)
    -- <:forallR
    (a, Forall E.KindedIdentifier{original,uuid=alpha,kind=alphaKind} b) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      let alphaTy' = IdentT ScopedIdentifier{scope=Local,uuid=alpha',original} alphaKind
      dropCtxForall alpha' <$>
        subtype (gamma :|> CtxForall alpha' alphaKind) a (typeSubst alphaTy' alpha b)
      
    -- <:forallL
    (Forall E.KindedIdentifier{uuid=alpha,kind=alphaKind} a, b) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      dropCtxMarker alpha' <$>
        subtype (gamma :|> CtxMarker alpha' :|> CtxExists alpha' alphaKind)
                (typeSubst (Exists alpha' alphaKind) alpha a)
                b

    -- <:InstantiateL
    (Exists alpha alphaKind, a)
      | alpha `elem` existentials gamma
      , alpha `S.notMember` freeTVars a
        -> instantiateL gamma alpha alphaKind a
    -- <:InstantiateR
    (a, Exists alpha alphaKind)
      | alpha `elem` existentials gamma
      , alpha `S.notMember` freeTVars a
        -> instantiateR gamma a alpha alphaKind
    _ -> error $
      "subtype, don't know what to do with:\n" ++
      show gamma ++ "\n" ++
      show typ1 ++ "\n" ++
      show typ2

-- | The free type variables in a type
freeTVars :: Type -> S.Set Word64
freeTVars typ = case typ of
  IdentT ScopedIdentifier{scope,uuid} _ -> case scope of
    Global -> mempty
    Local -> S.singleton uuid
  Forall E.KindedIdentifier{uuid=v} t -> S.delete v $ freeTVars t
  Exists v _ -> S.singleton v
  Arr t1 t2 -> freeTVars t1 `mappend` freeTVars t2

-- | Algorithmic instantiation (right):
--   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
instantiateR :: Seq CtxElem -> Type -> Word64 -> E.Kind -> Typecheck (Seq CtxElem)
instantiateR gamma a alpha alphaKind =
  assertWellFormedType gamma a $ assertWellFormedType gamma (Exists alpha alphaKind) $
  if | monotype a -> solve gamma alpha alphaKind a
     | otherwise -> case a of
      -- InstRReach
      Exists beta betaKind
        | ordered gamma alpha beta ->
            solve gamma beta betaKind (Exists alpha alphaKind)
        | otherwise ->
            solve gamma alpha alphaKind (Exists beta betaKind)
      -- InstRArr
      Arr a1 a2   -> case alphaKind of
        E.ArrowK k1 k2 -> do
          alpha1 <- freshTVar
          alpha2 <- freshTVar
          theta <- instantiateL
            (insertAt gamma (CtxExists alpha alphaKind) $ Seq.fromList
              [ CtxExists alpha2 k2
              , CtxExists alpha1 k1
              , CtxExistsSolved alpha
                  ( Arr
                    (Exists alpha1 k1)
                    (Exists alpha2 k2)
                  ) alphaKind
              ]
            ) alpha1 k1 a1
          instantiateR theta (apply theta a2) alpha2 k2
        _ -> failWith ExpectedArrowKind
      -- InstRAIIL
      Forall E.KindedIdentifier{uuid=beta,kind=betaKind} b -> do
        -- Do alpha conversion to avoid clashes
        beta' <- freshTVar
        dropCtxMarker beta' <$>
          instantiateR (gamma :|> CtxMarker beta' :|> CtxExists beta' betaKind)
                       (typeSubst (Exists beta' betaKind) beta b)
                       alpha
                       alphaKind
      _ -> error $ "The impossible happened! instantiateR: " ++ show (gamma, a, alpha)

-- | Is the type a Monotype?
monotype :: Type -> Bool
monotype typ = case typ of
  IdentT{} -> True
  Forall{} -> False
  Exists{} -> True
  Arr t1 t2  -> monotype t1 && monotype t2

-- | Algorithmic instantiation (left):
--   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
instantiateL :: Seq CtxElem -> Word64 -> E.Kind -> Type -> Typecheck (Seq CtxElem)
instantiateL gamma alpha alphaKind a =
  assertWellFormedType gamma a $ assertWellFormedType gamma (Exists alpha alphaKind) $
  if | monotype a -> solve gamma alpha alphaKind a
     | otherwise -> case a of
      -- InstLReach
      Exists beta betaKind
        | ordered gamma alpha beta ->
            solve gamma beta betaKind (Exists alpha alphaKind)
        | otherwise ->
            solve gamma alpha alphaKind (Exists beta betaKind)
      -- InstLArr
      Arr a1 a2   -> case alphaKind of
        E.ArrowK k1 k2 -> do
          alpha1 <- freshTVar
          alpha2 <- freshTVar
          theta <- instantiateR
            (insertAt gamma (CtxExists alpha alphaKind) $ Seq.fromList
              [ CtxExists alpha2 k2
              , CtxExists alpha1 k1
              , CtxExistsSolved alpha
                  ( Arr (Exists alpha1 k1)
                        (Exists alpha2 k2)
                  ) (E.ArrowK k1 k2)
              ]
            ) a1 alpha1 k1
          instantiateL theta alpha2 k2 (apply theta a2)
        _ -> failWith ExpectedArrowKind
      -- InstLAIIR
      Forall E.KindedIdentifier{original,uuid=beta,kind} b -> do
        -- Do alpha conversion to avoid clashes
        beta' <- freshTVar
        let betaTy' = IdentT ScopedIdentifier{scope=Local,uuid=beta',original} kind
        dropCtxForall beta' <$>
          instantiateL (gamma :|> CtxForall beta' kind)
                       alpha
                       alphaKind
                       (typeSubst betaTy' beta b)
      _ -> error $ "The impossible happened! instantiateL: "
                ++ show (gamma, alpha, a)

-- | solve (ΓL,α^,ΓR) α^ τ = (ΓL,α^ = τ,ΓR)
-- TODO: Do we always need to do typewf in here? Probably not.
-- Precondition: tau is a monotype, no foralls in it
solve ::
     Seq CtxElem -> Word64 -> E.Kind -> Type
  -> Typecheck (Seq CtxElem)
solve gamma alpha alphaKind tau = if typewf gammaL tau
  then if alphaKind == tauKind
    then pure gamma'
    else failWith KindMismatch
  else error "solve: tau not well formed"
  where
  (gammaL, gammaR) = splitCtxExists alpha gamma
  gamma' = (gammaL :|> CtxExistsSolved alpha tau tauKind) <> gammaR
  tauKind = monotypeKind tau

monotypeKind :: Type -> Kind
monotypeKind = \case
  IdentT _ k -> k
  AppT _ _ _ k -> k
  Arr a b -> E.ArrowK (monotypeKind a) (monotypeKind b)
  TupleT xs -> E.TupleK (map monotypeKind xs)
  Forall{} -> error "monotypeKind: argument was not a monotype"
  Exists _ k -> k

-- | ordered Γ α β = True <=> Γ[α^][β^]
ordered :: Seq CtxElem -> Word64 -> Word64 -> Bool
ordered gamma alpha beta =
  let gammaL = dropCtxExists beta gamma
   in alpha `elem` existentials gammaL

builtinTerms :: Map Word64 Type
builtinTerms = Map.fromList
  [(2000,intBinOpType)
  ,(2001,intBinOpType)
  ,(2002,intBinOpType)
  ,(2010,intRelOpType)
  ]

-- No type constructors yet
builtinTypes :: Map Word64 Kind
builtinTypes = Map.fromList
  [(1000,E.IntK)
  ,(1003,E.IntK)
  ]

builtinNullaryConstructors :: Map Word64 Type
builtinNullaryConstructors = Map.fromList
  [ (7000, boolType)
  , (7001, boolType)
  ]

intBinOpType :: Type
intBinOpType = Arr (TupleT [intType,intType]) intType

intRelOpType :: Type
intRelOpType = Arr (TupleT [intType,intType]) boolType

intType :: Type
intType = IdentT ScopedIdentifier{original="Int",uuid=1000,scope=Global} E.IntK

boolType :: Type
boolType = IdentT ScopedIdentifier{original="Bool",uuid=1003,scope=Global} E.IntK

mapAccumM :: Monad m => (s -> a -> m (b,s)) -> s -> [a] -> m ([b],s)
mapAccumM f s0 as0 = go [] s0 as0 where
  go !acc !s [] = let !r = List.reverse acc in pure (r,s)
  go !acc !s (x : xs) = do
    (b,s') <- f s x
    go (b : acc) s' xs
