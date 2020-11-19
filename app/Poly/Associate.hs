{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}

module Poly.Associate
  ( associate
  , associateDeclaration
  , associateModule
  ) where

import Common (Exportedness(Exported))
import Control.Monad (forM)
import Data.Map (Map)
import Data.Text.Short (ShortText)
import Data.Int (Int64)
import Data.Word (Word64)

import qualified Poly.Unchained as Unchained
import qualified Poly.Resolved as Resolved
import qualified Data.Map.Strict as Map

data Stack
  = StackTerminal !Unchained.Term
  | StackCons !Unchained.Term !Resolved.InfixIdentifier !Stack

pair :: Unchained.Term -> Unchained.Term -> Unchained.Term
pair a b = Unchained.Tuple [a,b]

associateDeclaration ::
     Resolved.TermDeclaration
  -> Either String Unchained.TermDeclaration
associateDeclaration Resolved.TermDeclaration{name,type_,definition} = do 
  definition <- associate definition
  Right Unchained.TermDeclaration { name , type_, definition, exported = Exported}

associateModule ::
     Resolved.Module
  -> Either String Unchained.Module
associateModule Resolved.Module{terms} = do 
  terms' <- mapM associateDeclaration terms
  Right Unchained.Module { types = mempty, terms = terms' }

associate ::
     Resolved.Term
  -> Either String Unchained.Term
associate = \case
  Resolved.Var t -> Right (Unchained.Var t)
  Resolved.Integer t -> Right (Unchained.Integer t)
  Resolved.Tuple t -> Unchained.Tuple <$> mapM associate t
  Resolved.Lam v t -> Unchained.Lam v <$> associate t
  Resolved.Let v expr body -> Unchained.Let v <$> associate expr <*> associate body
  Resolved.Jump label arg -> Unchained.Jump label <$> associate arg
  Resolved.Rec retTy jpts rbody -> do
    jpts' <- mapM
      (\(Resolved.JoinPoint name arg ty body) -> do
        body' <- associate body
        pure (Unchained.JoinPoint name arg ty body')
      ) jpts
    rbody' <- associate rbody
    pure (Unchained.Rec retTy jpts' rbody')
  Resolved.Infixes hd xs -> do
    allSameGroup xs
    hd' <- associate hd
    shuntingYard (StackTerminal hd') xs
  Resolved.Case t alts -> do
    t' <- associate t
    alts' <- forM alts $ \Resolved.Alternative{pat,arm} -> do
      arm' <- associate arm
      pure Unchained.Alternative{pat,arm=arm'}
    pure (Unchained.Case t' alts')

allSameGroup :: Resolved.InfixChain -> Either String ()
allSameGroup = \case
  Resolved.InfixChainTerminal -> Right ()
  Resolved.InfixChainCons s _ xs -> case s of
    Resolved.Application -> allSameGroup xs
    Resolved.CustomOp Resolved.InfixIdentifier{group} -> allInGroup group xs

allInGroup :: Word64 -> Resolved.InfixChain -> Either String ()
allInGroup !g = \case
  Resolved.InfixChainTerminal -> Right ()
  Resolved.InfixChainCons s _ xs -> case s of
    Resolved.Application -> allInGroup g xs
    Resolved.CustomOp Resolved.InfixIdentifier{group} -> if g == group
      then allInGroup g xs
      else Left "mixed infix operators from different groups"
   

-- Variant of shunting yard algorithm described at https://www.reddit.com/r/learnprogramming/comments/3cybca/how_do_i_go_about_building_an_ast_from_an_infix/ct02uam?utm_source=share&utm_medium=web2x
-- Good summary of rules at http://mathcenter.oxford.emory.edu/site/cs171/shuntingYardAlgorithm/
shuntingYard ::
     Stack -- stack of operands and operators
  -> Resolved.InfixChain -- argument symbols
  -> Either String Unchained.Term
shuntingYard st0 = \case
  Resolved.InfixChainTerminal -> Right (popAll st0)
  Resolved.InfixChainCons opX term chain -> do
    term' <- associate term
    case opX of
      Resolved.Application -> shuntingYard (apLast term' st0) chain
      Resolved.CustomOp op -> popUntilGtThenPush st0 chain op term'

popAll :: 
     Stack -- stack of operands and operators
  -> Unchained.Term
popAll = \case
  StackTerminal t -> t
  StackCons t1 op st -> popAll (mergeLast op t1 st)

apLast :: Unchained.Term -> Stack -> Stack
apLast t = \case
  StackTerminal t0 -> StackTerminal (Unchained.App t0 t)
  StackCons t0 op0 st0 -> StackCons (Unchained.App t0 t) op0 st0

mergeLast :: Resolved.InfixIdentifier -> Unchained.Term -> Stack -> Stack
mergeLast op t = \case
  StackTerminal t0 -> StackTerminal
    (Unchained.App (Unchained.Var (infixIdentToScopedIdent op)) (pair t0 t))
  StackCons t0 op0 st0 -> StackCons
    (Unchained.App (Unchained.Var (infixIdentToScopedIdent op)) (pair t0 t)) op0 st0

popUntilGtThenPush ::
     Stack -- stack of operands and operators
  -> Resolved.InfixChain -- constant while recursing
  -> Resolved.InfixIdentifier -- operator we are comparing against, constant
  -> Unchained.Term -- term to push
  -> Either String Unchained.Term
popUntilGtThenPush st0 chain op@Resolved.InfixIdentifier{precedence=prec} t0 = case st0 of
  StackTerminal t -> shuntingYard (StackCons t0 op st0) chain
  StackCons t opTop@Resolved.InfixIdentifier{precedence=precTop} st1 ->
    case compare prec precTop of
      GT -> shuntingYard (StackCons t0 op st0) chain
      _ -> popUntilGtThenPush (mergeLast opTop t st1) chain op t0

infixIdentToScopedIdent :: Resolved.InfixIdentifier -> Resolved.ScopedIdentifier
infixIdentToScopedIdent Resolved.InfixIdentifier{original,uuid} =
  Resolved.ScopedIdentifier{original,uuid,scope=Resolved.Global}
  
