{-# language DuplicateRecordFields #-}

module Poly.Unresolved
  ( Term(..)
  , TermDeclaration(..)
  , Module(..)
  , Import(..)
  , Type(..)
  ) where

import Common (Exportedness)
import Data.Text.Short (ShortText)
import Data.Int (Int64)
import Data.Primitive (SmallArray)
import Data.Primitive.Unlifted.Array (UnliftedArray)

data Type = Type
  deriving (Show)
data TypeDeclaration = TypeDeclaration
  deriving (Show)

data Term
  = Var !ShortText
  | Lam !ShortText !Term
  | App !Term !Term
  | Tuple ![Term]
  | Integer !Int64
  deriving (Show)

data Module = Module
  { imports :: !(SmallArray Import)
  , types :: !(SmallArray TypeDeclaration)
  , terms :: !(SmallArray TermDeclaration)
  } deriving (Show)

data TermDeclaration = TermDeclaration
  { name :: !ShortText
  , type_ :: !Type
  , body :: !Term
  , exported :: !Exportedness
  } deriving (Show)

data Import = Import
  { module_ :: !ShortText
  , identifiers :: !(UnliftedArray ShortText)
  } deriving (Show)
