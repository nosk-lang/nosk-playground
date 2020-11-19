{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}

module Poly.Unchained
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
  , Deconstruction(..)
  -- Builtins
  -- , builtinTerms
  ) where

import Common (Exportedness)
import Data.Text.Short (ShortText)
import Data.Int (Int64)
import Data.Word (Word64)

import Data.Primitive (SmallArray)
import Poly.Resolved (Identifier(..),ScopedIdentifier(..),Scope(..),TypeScheme(..),Type(..),Pattern,KindedIdentifier(..),Kind(..),Pattern(..),Constructor(..),Deconstruction(..))

import Data.Map (Map)

import qualified Data.Map.Strict as Map

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
    -- ^ Infix operators are not allowed in types, so unchaining leaves
    -- types alone.
  , definition :: !Term
  , exported :: !Exportedness
  } deriving (Show)

data Alternative = Alternative
  { pat :: !Pattern
  , arm :: !Term
  } deriving (Show)
