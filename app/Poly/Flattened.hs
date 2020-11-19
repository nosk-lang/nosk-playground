{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language LambdaCase #-}

module Poly.Flattened
  ( Term(..)
  , Type(..)
  , TypeScheme(..)
  , TermDeclaration(..)
  , Identifier(..)
  , ScopedIdentifier(..)
  , Scope(..)
  , Module(..)
  , JoinPoint(..)
  , Alternative(..)
  , KindedIdentifier(..)
  , Kind(..)
  , Pattern(..)
  , Constructor(..)
  -- Functions
  , flatten
  , flattenModule
  ) where

import Control.Applicative (liftA2)
import Common (Exportedness(Exported))
import Data.Text.Short (ShortText)
import Data.Int (Int64)
import Data.Word (Word64)

import Data.Primitive (SmallArray)
import Poly.Resolved (Identifier(..),ScopedIdentifier(..),Scope(..),TypeScheme(..),Type(..),Pattern,KindedIdentifier(..),Kind(..),Pattern(..),Constructor(..))

import Data.Map (Map)

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (get,put,State,StateT,runStateT,runState)
import qualified Data.Map.Strict as Map
import qualified Poly.Unchained as E

data TypeDeclaration = TypeDeclaration
  deriving (Show)

data Term
  = Var !ScopedIdentifier
  | Lam !Identifier !Term
  | Let !Identifier !Term !Term
  | App !Term !Term
  | Integer !Int64
  | Tuple [Term]
  | Rec !Type [JoinPoint] !Term
  | Jump !Identifier !Term
  | Case !Term [Alternative]
  deriving (Show)

data Module = Module
  { types :: !(SmallArray TypeDeclaration)
  , terms :: !(SmallArray TermDeclaration)
  } deriving (Show)

data JoinPoint = JoinPoint
  { name :: !Identifier
  , argument :: !Identifier
  , argumentType :: !Type
  , body :: !Term
  } deriving (Show)

data TermDeclaration = TermDeclaration
  { name :: !ShortText
  , type_ :: !TypeScheme
  , definition :: !Term
  , exported :: !Exportedness
  } deriving (Show)

data Alternative = Alternative
  { constructor :: !Constructor
  , bindings :: ![Identifier]
  , arm :: !Term
  } deriving (Show)

flattenModule ::
     E.Module
  -> Module
flattenModule E.Module{terms} =
  let terms' = fmap flattenDeclaration terms
   in Module { types = mempty, terms = terms' }

flattenDeclaration ::
     E.TermDeclaration
  -> TermDeclaration
flattenDeclaration E.TermDeclaration{name,type_,definition} =
  let definition' = flatten definition
   in TermDeclaration { name , type_, definition=definition', exported = Exported}

flatten :: E.Term -> Term
flatten x0 = fst (runState (go x0) 1000000) where
  go (E.Var v) = pure (Var v)
  go (E.Lam v b) = fmap (Lam v) (go b)
  go (E.Let v e b) = liftA2 (Let v) (go e) (go b)
  go (E.App a b) = liftA2 App (go a) (go b)
  go (E.Integer i) = pure (Integer i)
  go (E.Tuple xs) = fmap Tuple (mapM go xs)
  go (E.Case e alts) = do
    e' <- go e
    alts' <- mapM goTupleAlt alts
    pure (Case e' alts')
  go (E.Rec ty jpts e) = do
    jpts' <- mapM goJoinPoint jpts
    e' <- go e
    pure (Rec ty jpts' e')
  go (E.Jump ident e) = do
    e' <- go e
    pure (Jump ident e')
  goJoinPoint :: E.JoinPoint -> State Word64 JoinPoint
  goJoinPoint E.JoinPoint{name,argument,argumentType,body} = do
    body' <- go body
    pure JoinPoint{name,argument,argumentType,body=body'}
  goTupleAlt :: E.Alternative -> State Word64 Alternative
  goTupleAlt E.Alternative{pat,arm} = case pat of
    -- TODO: destroy PatternVariable here
    E.PatternVariable x -> error "flatten: figure out what to do"
    E.PatternDeconstruction (E.Deconstruction ctor bindings) -> case ctor of
      E.TupleConstructor -> do
        arm' <- go arm
        (bindings',arm'') <- runStateT (mapM goTuplePat bindings) arm'
        pure Alternative{constructor=E.TupleConstructor,bindings=bindings',arm=arm''}
      E.CustomConstructor x -> case bindings of
        [] -> do
          arm' <- go arm
          pure (Alternative ctor [] arm')
        _ -> error "Poly.Flattened: figure out non-nullary constructors"
  goTuplePat :: E.Pattern -> StateT Term (State Word64) Identifier
  goTuplePat = \case
    E.PatternVariable x -> pure x
    E.PatternDeconstruction (E.Deconstruction E.TupleConstructor bindings) -> do
      !uuid <- lift get
      lift (put (uuid + 1))
      bindings' <- mapM goTuplePat bindings
      arm <- get
      put $ Case (Var (ScopedIdentifier{uuid,original="unknown",scope=Local}))
        [Alternative{constructor=TupleConstructor,bindings=bindings',arm}]
      pure Identifier{uuid,original="unknown"}
