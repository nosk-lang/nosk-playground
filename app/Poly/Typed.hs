{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}

-- This might not be needed.

module Poly.Typed
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
  ) where

data Term
  = Var !ScopedIdentifier
  | Lam !Identifier !Term
  | Let !Identifier !Term !Term
  | App !Term !Term
  | Integer !Int64
  | Tuple [Term]
  | Rec [JoinPoint] !Term
  | Jump !Identifier !ScopedIdentifier
  | Case !Term [Alternative]
  deriving (Show)
