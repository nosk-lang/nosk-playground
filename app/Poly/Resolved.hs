{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}

module Poly.Resolved
  ( Term(..)
  , TermDeclaration(..)
  , Identifier(..)
  , ScopedIdentifier(..)
  , Scope(..)
  , Type(..)
  , Kind(..)
  , Module(..)
  , InfixChain(..)
  , InfixIdentifier(..)
  , KindedIdentifier(..)
  , ScopedOp(..)
  , TypeScheme(..)
  , Pattern(..)
  , Alternative(..)
  , Deconstruction(..)
  , Constructor(..)
  , JoinPoint(..)
  ) where

import Common (Exportedness)
import Data.Text.Short (ShortText)
import Data.Int (Int64)
import Data.Word (Word64,Word8)

import Data.Primitive (SmallArray)

data TypeScheme = TypeScheme
  { representations :: ![Identifier]
  , type_ :: !Type
  } deriving (Show)

data Type
  = IdentT !ScopedIdentifier
  | AppT !Type !Type
  | Arr !Type !Type
  | TupleT [Type] 
  | Forall !KindedIdentifier !Type
  deriving (Show,Eq)

data Kind
  = IdentK !ScopedIdentifier
  | TupleK [Kind] 
  | IntK
  | ArrowK !Kind !Kind
  deriving (Show,Eq)

-- data KindIdent
--   = KindIdentVar !Identifier
--   | KindIdentPrimitive !KindPrim
-- 
-- data KindPrim
--   = KindInt
--   | KindBoxed

data Term
  = Var !ScopedIdentifier
  | Lam !Identifier !Term
  | Infixes !Term !InfixChain
  | Integer !Int64
  | Tuple ![Term]
  | Let !Identifier !Term !Term
  | Case !Term [Alternative]
  | Rec !Type [JoinPoint] !Term
  | Jump !Identifier !Term
    -- ^ Note: join points are never global
  deriving (Show)

data JoinPoint = JoinPoint
  { name :: !Identifier
  , argument :: !Identifier
  , argumentType :: !Type
  , body :: !Term
  } deriving (Show)

data InfixChain
  = InfixChainTerminal
  | InfixChainCons !ScopedOp !Term !InfixChain
  deriving (Show)

-- | Used for functions names (not infix ones though)
-- and data constructors.
data Identifier = Identifier
  { original :: !ShortText
    -- ^ What was originally written in the source code.
  , uuid :: !Word64
  } deriving (Show)

instance Eq Identifier where
  Identifier{uuid=ua} == Identifier{uuid=ub} = ua == ub


-- | Used for type variables.
data KindedIdentifier = KindedIdentifier
  { original :: !ShortText
    -- ^ What was originally written in the source code.
  , uuid :: !Word64
    -- ^ UUID of the type.
  , kind :: !Kind
    -- ^ The kind of the type
  } deriving (Show)

instance Eq KindedIdentifier where
  KindedIdentifier{uuid=ua} == KindedIdentifier{uuid=ub} = ua == ub

data ScopedOp
  = Application
  | CustomOp !InfixIdentifier
  deriving (Show)

-- TODO: Possibly add prefix name. Not sure if this is actually needed.
data InfixIdentifier = InfixIdentifier
  { original :: !ShortText
    -- ^ What was originally written in the source code.
  , uuid :: !Word64
    -- ^ A UUID (only unique within its scope)
  , group :: !Word64
    -- ^ UUID of the group that this infix operator belongs to.
    -- Infix groups restrict which operators can be used together.
  , precedence :: !Word8
  } deriving (Show)

data ScopedIdentifier = ScopedIdentifier
  { original :: !ShortText
    -- ^ What was originally written in the source code.
  , uuid :: !Word64
    -- ^ A UUID (only unique within its scope)
  , scope :: !Scope
  } deriving (Show)

instance Eq ScopedIdentifier where
  ScopedIdentifier{scope=sa,uuid=ua} == ScopedIdentifier{scope=sb,uuid=ub} =
    sa == sb && ua == ub

data Scope = Global | Local
  deriving (Show,Eq)

data Module = Module
  { types :: !(SmallArray TypeDeclaration)
  , terms :: !(SmallArray TermDeclaration)
  } deriving (Show)

data TermDeclaration = TermDeclaration
  { name :: !ShortText
  , type_ :: !TypeScheme
  , definition :: !Term
  , exported :: !Exportedness
  } deriving (Show)

data Alternative = Alternative
  { pat :: !Pattern
  , arm :: !Term
  } deriving (Show)

data Pattern
  = PatternVariable !Identifier
  | PatternDeconstruction !Deconstruction
  deriving (Show)

data Deconstruction = Deconstruction
  { constructor :: Constructor
  , bindings :: [Pattern]
  } deriving (Show)

data Constructor
  = CustomConstructor !Identifier
  | TupleConstructor
  deriving (Show)

data TypeDeclaration = TypeDeclaration
  { name :: !Identifier
  , kind :: !Kind
  , constructors :: !(SmallArray ConstructorDeclaration)
  } deriving (Show)

data ConstructorDeclaration = ConstructorDeclaration
  { name :: !Identifier
  , argument :: !ConstructorArgument
  }
  deriving (Show)

data ConstructorArgument
  = ConstructorArgumentNone
  | ConstructorArgumentSome !Type
  deriving (Show)
