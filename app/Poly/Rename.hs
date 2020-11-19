{-# language BangPatterns #-}
{-# language DerivingStrategies #-}
{-# language DeriveFunctor #-}
{-# language DuplicateRecordFields #-}
{-# language LambdaCase #-}
{-# language MultiWayIf #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}

module Poly.Rename
  ( module_
  , renameModule
  ) where

import Common (Exportedness(..))
import Control.Applicative (liftA2)
import Data.Text.Short (ShortText)
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import Data.Foldable (foldlM)
import Poly.Resolved (Term,Identifier(Identifier))
import Poly.Resolved (ScopedIdentifier(ScopedIdentifier),Scope(Global,Local))
import Data.Map (Map)
import Control.Monad.Trans.State.Strict (StateT,runStateT)
import Control.Monad.Trans.Class (lift)

import qualified Data.Primitive.Unlifted.Array as PM
import qualified Poly.Resolved as Resolved
import qualified Poly.Syntax as Syntax
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import qualified Control.Monad.Trans.State.Strict as State

data RenameError
  = UnknownIdentifier !ShortText
  | UnknownKindIdentifier !ShortText
  | UnknownLabel !ShortText
  | UnknownInfixIdentifier !ShortText
  | UnknownDataConstructor !ShortText
  | UnknownModule !ShortText
  | ShadowedIdentifier !ShortText
  | ModuleDoesNotExport !ShortText !(Syntax.Import)
  deriving stock (Show)

-- The Word64 argument is the UUID source. It is incremented at
-- binding sites.
data Rename a = Rename (Word64 -> RenameResult a)
  deriving stock (Functor)

instance Applicative Rename where
  pure a = Rename (\w -> RenameSuccess w a)
  r1 <*> r2 = bindRename r1 $ \x -> bindRename r2 $ \y -> pure (x y)

instance Monad Rename where
  (>>=) = bindRename

bindRename :: Rename a -> (a -> Rename b) -> Rename b
bindRename (Rename f) g = Rename $ \w0 -> case f w0 of
  RenameSuccess w1 a -> case g a of
    Rename h -> h w1
  RenameFailure e -> RenameFailure e

data RenameResult a
  = RenameSuccess !Word64 !a
  | RenameFailure !RenameError
  deriving stock (Functor)

failWith :: RenameError -> Rename a
failWith e = Rename (\ !_ -> RenameFailure e)

nextUuid :: Rename Word64
nextUuid = Rename (\ !w -> RenameSuccess (w + 1) w)

renameModule :: Syntax.Module -> Either RenameError Resolved.Module
renameModule u = case module_ Map.empty u of
  Rename f -> case f 0 of
    RenameSuccess _ r -> Right r
    RenameFailure e -> Left e

data Maps = Maps
  { terms :: !(Map ShortText Word64)
  , types :: !(Map ShortText Word64)
  , infixes :: !(Map ShortText Resolved.InfixIdentifier)
  }

emptyMaps :: Maps
emptyMaps = Maps Map.empty Map.empty Map.empty

importIdentifier ::
     ShortText
  -> Syntax.Import -- identifier to import
  -> Maps -- source module
  -> Maps -- in-scope identifier map being built 
  -> Rename Maps -- updated in-scope identifier map
importIdentifier !mdlName !imp !m !acc = case imp of
  Syntax.ImportInfix ident -> do
    let Maps{infixes=exports} = m
    uuid <- maybe (failWith err) pure (Map.lookup ident exports)
    let Maps{infixes=old} = m
    pure m{infixes=Map.insert ident uuid old}
  Syntax.ImportType ident -> do
    let Maps{types=exports} = m
    uuid <- maybe (failWith err) pure (Map.lookup ident exports)
    let Maps{types=old} = m
    pure m{types=Map.insert ident uuid old}
  where
  err = ModuleDoesNotExport mdlName imp

builtinExps :: Maps
builtinExps = Maps
  { terms = Map.fromList
      [ ("add",2000)
      , ("multiply",2001)
      , ("subtract",2002)
      , ("greaterThan",2010)
      ]
  , types = Map.fromList
      [ ("Int",1000)
      , ("Option",1001)
      , ("List",1002)
      , ("Bool",1003)
      ]
  , infixes = Map.fromList
      [ ("+",Resolved.InfixIdentifier "+" 2000 100 50)
      , ("*",Resolved.InfixIdentifier "*" 2001 100 49)
      , ("-",Resolved.InfixIdentifier "-" 2002 100 50)
      , (">?",Resolved.InfixIdentifier ">?" 2010 100 70)
      ]
  }

-- TODO: Thread this through properly rather than just looking
-- it up when renaming patterns.
builtinConstructors :: Map ShortText Word64
builtinConstructors = Map.fromList
  [ ("True", 7000)
  , ("False", 7001)
  ]

builtinReps :: Map ShortText Word64
builtinReps = Map.fromList
  [ ("Word",3000)
  , ("Box",3001)
  ]

module_ ::
     Map ShortText Maps
     -- ^ Maps for identifiers exported from other modules
  -> Syntax.Module
  -> Rename Resolved.Module
module_ world Syntax.Module{imports,terms,types} = do
  globals0@Maps{terms=globalTerms0} <- foldlM
    ( \ !acc0 Syntax.ImportStatement{module_=m,imports} -> do
      exports <- case Map.lookup m world of
        Just exps -> pure exps
        Nothing
          | m == "Builtin" -> pure builtinExps
          | otherwise -> failWith (UnknownModule m)
      foldlM
        ( \ !acc !imp -> importIdentifier m imp exports acc
        ) acc0 imports
    ) emptyMaps imports
  globalTerms1 <- foldlM
    ( \ !acc0 Syntax.TermDeclaration{name} -> do
      uuid <- nextUuid
      pure (Map.insert name uuid acc0)
    ) globalTerms0 terms
  -- TODO: handle types
  let globals1 = globals0{terms=globalTerms1}
  -- TODO: traverse is awful on SmallArray
  terms' <- traverse (termDeclaration globals1) terms
  pure Resolved.Module{types=mempty,terms=terms'}

termDeclaration ::
     Maps -- Resolves global identifiers to UUID
  -> Syntax.TermDeclaration
  -> Rename Resolved.TermDeclaration
termDeclaration !globals !t0 = do
  (type_',repVariables) <- resolveTypeScheme (types globals) type_
  definition' <- term repVariables globals definition
  pure (Resolved.TermDeclaration{name,type_=type_',definition=definition',exported=Exported})
  where
  Syntax.TermDeclaration{name,type_,definition} = t0

-- TODO: handle TypeVarsNone correctly. Pull out the variables
-- into a forall.
-- Return both a type scheme and all of the representation variables.
-- All the rep vars are in scope in the body.
resolveTypeScheme ::
     Map ShortText Word64
  -> Syntax.TypeScheme
  -> Rename (Resolved.TypeScheme, Map ShortText Word64)
resolveTypeScheme !globals = \case
  Syntax.TypeSchemeExplicitReps reps typ -> do
    let (representations,repLocals,repCount) = numberReps reps
    -- (variables,locals) <- resolveExplicitRepTypes repCount repLocals tys
    type_ <- resolveType repLocals globals typ 
    pure (Resolved.TypeScheme{representations,type_},repLocals)
  -- ImplicitReps currently never happens.
  Syntax.TypeSchemeImplicitReps _ -> error "resolveTypeScheme: implicit reps, rethink"

-- Syntax.TypeScheme{variables,type_} = case variables of
--   Syntax.TypeVarsNone -> do
--     type_' <- resolveType globals Map.empty type_ 
--     pure Resolved.TypeScheme{representations=[],variables=[],type_=type_'}
--   Syntax.TypeVarsImplicitReps{} -> error "resolveTypeScheme: handle TypeVarsImplicitReps"
--   Syntax.TypeVarsExplicitReps reps tys -> do

-- Creates type variable list and a map for lookup.
numberReps :: [ShortText] -> ([Identifier],Map ShortText Word64,Word64)
numberReps = go 0 [] Map.empty where
  go !uuid !acc !accB [] = (List.reverse acc, accB, uuid)
  go !uuid !acc !accB (original : xs) =
    go (uuid + 1) (Identifier{original,uuid} : acc) (Map.insert original uuid accB) xs

resolveType ::
     Map ShortText Word64
  -> Map ShortText Word64
  -> Syntax.Type Syntax.ExplicitlyKindedVar
  -> Rename Resolved.Type
resolveType !repVariables !globals = go Map.empty where
  go :: Map ShortText Word64
     -> Syntax.Type Syntax.ExplicitlyKindedVar
     -> Rename Resolved.Type
  go !vars (Syntax.VarT original) = case Map.lookup original vars of
    Nothing -> failWith (UnknownInfixIdentifier original)
    Just uuid -> pure (Resolved.IdentT Resolved.ScopedIdentifier{uuid,original,scope=Local})
  go !vars (Syntax.Constant original) = case Map.lookup original globals of
    Nothing -> failWith (UnknownInfixIdentifier original)
    Just uuid -> pure (Resolved.IdentT Resolved.ScopedIdentifier{uuid,original,scope=Global})
  go !vars (Syntax.Arr x y) = liftA2 Resolved.Arr (go vars x) (go vars y)
  go !vars (Syntax.AppT x y) = liftA2 Resolved.AppT (go vars x) (go vars y)
  go !vars (Syntax.TupleT ts) = Resolved.TupleT <$> mapM (go vars) ts
  go !vars (Syntax.Forall [] t) = go vars t
  go !vars (Syntax.Forall (Syntax.ExplicitlyKindedVar original k : vs) t) = do
    uuid <- nextUuid
    kind <- case k of
      Syntax.VarK kvar -> do
        kuuid <- maybe (failWith (UnknownKindIdentifier kvar)) pure (Map.lookup kvar repVariables)
        pure $! Resolved.IdentK ScopedIdentifier{original=kvar,uuid=kuuid,scope=Local}
      Syntax.ConstantK kconst -> do
        kuuid <- maybe (failWith (UnknownKindIdentifier kconst)) pure (Map.lookup kconst builtinReps)
        pure $! Resolved.IdentK ScopedIdentifier{original=kconst,uuid=kuuid,scope=Global}
    vs' <- go (Map.insert original uuid vars) (Syntax.Forall vs t)
    pure (Resolved.Forall Resolved.KindedIdentifier{original,uuid,kind} vs')
    

-- -- TODO: add kinds to the global map as well.
-- resolveExplicitRepTypes ::
--      Word64
--   -> Map ShortText Word64
--   -> [Syntax.ExplicitlyKindedVar]
--   -> Rename ([Resolved.KindedIdentifier],Map ShortText Word64)
-- resolveExplicitRepTypes !uuid0 !variables !reps0 = go reps0 uuid0 [] Map.empty where
--   go [] !_ !tys !m = pure (List.reverse tys,m)
--   go (Syntax.TypeVar name rep : tvs) !uuid !tys !m = do
--     let uuid' = uuid + 1
--     let m' = Map.insert name uuid m
--     case rep of
--       Syntax.ExplicitRepVar original -> case Map.lookup original variables of
--         Nothing -> failWith (UnknownKindIdentifier original)
--         Just kindUuid -> do
--           let !kind = Resolved.IdentK ScopedIdentifier{original,uuid=kindUuid,scope=Local}
--           let !kident = Resolved.KindedIdentifier{original=name,uuid,kind}
--           go tvs uuid' (kident : tys) m'
--       Syntax.ExplicitRepConstant{} -> error "TODO: support constant rep in renamer"


data JoinPointUuid = JoinPointUuid !Syntax.JoinPoint !Word64

term ::
     Map ShortText Word64 -- Resolves representation variables
  -> Maps -- Resolves global identifiers to UUID
  -> Syntax.Term
  -> Rename Resolved.Term
term !repVariables !globals !t0 = go Map.empty Map.empty t0 where
  go :: 
       Map ShortText Word64 -- Resolves local identifiers to UUID
    -> Map ShortText Word64 -- Resolves join points (labels) to UUIDs
    -> Syntax.Term
    -> Rename Resolved.Term
  go !locals !labels (Syntax.Case expr alts) = do
    expr' <- go locals labels expr
    alts' <- mapM (goAlternative locals labels) alts
    pure (Resolved.Case expr' alts')
  go !locals !labels (Syntax.Tuple ts) = do
    ts' <- mapM (go locals labels) ts
    pure (Resolved.Tuple ts')
  go !locals !_ (Syntax.Var original)
    | Just uuid <- Map.lookup original locals =
        pure (Resolved.Var ScopedIdentifier{original,uuid,scope=Local})
    | Just uuid <- Map.lookup original (terms globals) =
        pure (Resolved.Var ScopedIdentifier{original,uuid,scope=Global})
    | otherwise = failWith (UnknownIdentifier original)
  go !locals !labels (Syntax.Infixes chainHead chain) = liftA2 Resolved.Infixes
    (go locals labels chainHead)
    (goChain locals labels chain)
  go !locals !labels (Syntax.Lam original e) = do
    uuid <- nextUuid
    locals' <- addResolution original uuid locals
    e' <- go locals' labels e
    let ident = Identifier{original,uuid}
    pure (Resolved.Lam ident e')
  go !locals !labels (Syntax.Let original expr body) = do
    expr' <- go locals labels expr
    uuid <- nextUuid
    locals' <- addResolution original uuid locals
    body' <- go locals' labels body
    let ident = Identifier{original,uuid}
    pure (Resolved.Let ident expr' body')
  go !locals !labels (Syntax.Jump label arg)
    | Just labelUuid <- Map.lookup label labels = do
      let labelIdent = Identifier{original=label,uuid=labelUuid}
      arg' <- go locals labels arg
      pure (Resolved.Jump labelIdent arg')
    | otherwise = failWith (UnknownLabel label)
  go !locals !labels (Syntax.Rec resultTy jpts rbody) = do
    resultTy' <- resolveType repVariables (types globals) resultTy
    -- I'm not sure if this reverses the recursive bindings. It doesn't
    -- matter if it does though.
    (!labels', !jpts') <- foldlM
      (\ (labels0,jpts0) jpt@Syntax.JoinPoint{name} -> do
        uuid <- nextUuid
        labels1 <- addResolution name uuid labels0
        let !jpt' = JoinPointUuid jpt uuid
        let !jpts1 = jpt' : jpts0
        pure (labels1,jpts1)
      ) (labels,[]) jpts
    !jpts'' <- mapM
      ( \(JoinPointUuid Syntax.JoinPoint{name,argument,argumentType,body} labelUuid) -> do
        let !name' = Identifier{original=name,uuid=labelUuid}
        uuid <- nextUuid
        let !argument' = Identifier{original=argument,uuid}
        locals' <- addResolution argument uuid locals
        argumentType' <- resolveType repVariables (types globals) argumentType
        body' <- go locals' labels' body
        pure Resolved.JoinPoint
          { name=name'
          , argumentType=argumentType'
          , argument=argument'
          , body=body'
          }
      ) jpts'
    !rbody' <- go locals labels' rbody
    pure $! Resolved.Rec resultTy' jpts'' rbody'
  go !_ !_ (Syntax.Integer i) = pure (Resolved.Integer i)
  goChain :: Map ShortText Word64 -> Map ShortText Word64 -> Syntax.InfixChain -> Rename Resolved.InfixChain
  goChain !_ !_ Syntax.InfixChainTerminal = pure Resolved.InfixChainTerminal
  goChain !locals !labels (Syntax.InfixChainCons op t cs) = do
    t' <- go locals labels t
    let Maps{infixes} = globals
    op' <- case op of
      Syntax.Application -> pure Resolved.Application
      Syntax.CustomOp name -> case Map.lookup name infixes of
        Nothing -> failWith (UnknownInfixIdentifier name)
        Just ident -> pure (Resolved.CustomOp ident)
    cs' <- goChain locals labels cs
    pure (Resolved.InfixChainCons op' t' cs')
  goAlternative ::
       Map ShortText Word64
    -> Map ShortText Word64
    -> Syntax.Alternative
    -> Rename Resolved.Alternative
  goAlternative !locals !labels (Syntax.Alternative{pat,arm}) = do
    (pat',locals') <- runStateT (goPattern pat) locals
    arm' <- go locals' labels arm
    pure Resolved.Alternative{pat=pat',arm=arm'}
  goPattern ::
       Syntax.Pattern
    -> StateT (Map ShortText Word64) Rename Resolved.Pattern
  goPattern = \case
    Syntax.PatternVariable original -> do
      uuid <- lift nextUuid
      locals <- State.get
      -- TODO: Consider warning or failing when name shadowing happens.
      let locals' = Map.insert original uuid locals
      State.put locals'
      pure (Resolved.PatternVariable Identifier{original,uuid})
    Syntax.PatternDeconstruction Syntax.Deconstruction{constructor,bindings} -> do
      constructor' <- case constructor of
        Syntax.TupleConstructor -> pure Resolved.TupleConstructor
        Syntax.CustomConstructor original ->
          case Map.lookup original builtinConstructors of
            Nothing -> lift (failWith (UnknownDataConstructor original))
            Just uuid -> pure (Resolved.CustomConstructor Identifier{uuid,original})
      bindings' <- mapM goPattern bindings
      pure
        ( Resolved.PatternDeconstruction Resolved.Deconstruction
          {constructor=constructor',bindings=bindings'}
        )
      
-- identifyVariables ::
--      [ShortText]
--   -> Map ShortText Word64
--   -> Rename (Map ShortText Word64)
-- identifyVariables = go
--   go [] !acc = acc
--   go (t : ts) !acc = do
--     uuid <- nextUuid
--     -- TODO: Consider warning or failing when name shadowing happens.
--     let !acc' = Map.insert original uuid acc
--     pure acc'

addResolution ::
     ShortText
  -> Word64
  -> Map ShortText Word64
  -> Rename (Map ShortText Word64)
addResolution !original !uuid !identifiers = Map.alterF
  (\x -> case x of
    Nothing -> pure $! Just $! uuid
    Just _ -> failWith $! ShadowedIdentifier original
  ) original identifiers
