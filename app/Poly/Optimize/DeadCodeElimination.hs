{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}

-- This remove let bindings that are unused. The current implementation
-- is only semantics-preserving for a lazy language.
module Poly.Optimize.DeadCodeElimination
  ( module_
  , termDecl
  , term
  ) where

import Control.Applicative (liftA2)
import Poly.Flattened (Term,TermDeclaration(TermDeclaration),Alternative(Alternative))
import Poly.Flattened (Module(Module))
import Data.Set (Set)
import Data.Word (Word64)
import Control.Monad.Trans.Writer.CPS (Writer,tell,runWriter)

import qualified Data.Set as Set
import qualified Poly.Flattened as E

data Result = Result
  !(Set Word64) -- Identifiers that were referred to
  !Term -- optimized expression

module_ :: Module -> Module
module_ Module{types,terms} =
  Module{types,terms=fmap termDecl terms}

termDecl :: TermDeclaration -> TermDeclaration
termDecl TermDeclaration{name,type_,definition,exported} =
  TermDeclaration{name,type_,definition=term definition,exported}

term :: Term -> Term
term x = let (t,_) = runWriter (worker x) in t

worker :: Term -> Writer (Set Word64) Term
worker !e0 = case e0 of
  E.Var E.ScopedIdentifier{uuid} -> do
    tell (Set.singleton uuid)
    pure e0
  E.Let ident@E.Identifier{uuid} expr body -> do
    let (body',bodyUuids) = runWriter (worker body)
    tell bodyUuids
    if Set.member uuid bodyUuids
      then do
        expr' <- worker expr
        pure (E.Let ident expr' body')
      else pure body'
  E.App a b -> liftA2 E.App (worker a) (worker b)
  E.Integer{} -> pure e0
  E.Tuple ts -> E.Tuple <$> mapM worker ts
  E.Lam ident t -> E.Lam ident <$> worker t
  E.Case expr alts -> do
    expr' <- worker expr
    alts' <- mapM workerAlt alts
    pure (E.Case expr' alts') 

workerAlt :: Alternative -> Writer (Set Word64) Alternative
workerAlt Alternative{constructor,bindings,arm} = do
  arm' <- worker arm
  pure Alternative{constructor,bindings,arm=arm'}
