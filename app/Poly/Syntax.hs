{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language LambdaCase #-}

module Poly.Syntax
  ( decodeModule
  , decodeDeclaration
  , Term(..)
  , InfixChain(..)
  , Op(..)
  , TermDeclaration(..)
  , Pattern(..)
  , Alternative(..)
  , Module(..)
  , Import(..)
  , ImportStatement(..)
  , TypeScheme(..)
  , Type(..)
  , Constructor(..)
  , Deconstruction(..)
  , JoinPoint(..)
  , ExplicitRep(..)
  , ExplicitlyKindedVar(..)
  , Kind(..)
  , TypeDeclaration(..)
  ) where

import Control.Applicative (liftA2)
import Data.Parser (Parser)
import Data.Primitive (SmallArray)
import Data.Text.Short (ShortText)
import Poly.Token (Token)
import Data.Int (Int64)
import Data.Primitive.Unlifted.Array (UnliftedArray,MutableUnliftedArray)
import Data.Builder.ST (Builder)
import Data.Chunks (Chunks)
import Data.List.NonEmpty (NonEmpty((:|)))

import qualified Data.Chunks as Chunks
import qualified Data.List as List
import qualified Data.Builder.ST as Builder
import qualified Data.Parser as Parser
import qualified Data.Primitive.Unlifted.Array as PM
import qualified Poly.Token as T

-- module declaration
--   | module name ( exports0 where imports declarations
-- exports0
--   | )
--   | name exports1
-- exports1
--   | )
--   | , name exports1
-- import
--   | uppername ( identifiers )
-- declaration
--   | declare name : typescheme as termchain0
-- typescheme
--   | forall repvars . forall quantified . typechain0
--   | forall quantified typechain0
--   | typechain0
-- repvars
--   | var repvars
--   | .
-- quantified
--   | ( var : repname ) quantified
--   | .
-- typechain0
--   | type typechain1
--   | forall vars. type typechain1
-- typechain1
--   | -> type typechain1
--   | -> forall vars. type typechain1
--   | empty
-- type
--   | ( typechain0 )
--   | constant typearg? // constant type or type application
--   | var
--   | < typetuple0
-- typearg
--   | ( typechain0 )
--   | constant
--   | var
--   | < typetuple0
-- typetuple0
--   | >
--   | typechain0 typetuple1
-- typetuple1
--   | >
--   | , typechain0 typetuple1
-- termchain0
--   | term termchain1
-- termchain1
--   | infixop term termchain1 // infix operator
--   | term termchain1 // function application
--   | empty
-- term
--   | lambda var arrow termchain0
--   | let var equals termchain0 in termchain0
--   | var
--   | int
--   | string
--   | < tuple0
--   | ( termchain0 )
--   | case termchain0 of { alts0
--   | rec { label0 labels1 in termchain0
-- tuple0
--   | >
--   | termchain0
-- tuple1
--   | >
--   | , termchain0 tuple1
-- labels1
--   | }
--   | , label0 labels1
-- label0
--   | label var var equals termchain0
-- alts0
--   | }
--   | alt alts1
-- alts1
--   | ; alts1
--   | } 
-- alt
--   | pattern -> term
-- pattern
--   | < tuplepat0
--   | datacon patterns
--   | var
--   | ( pattern )
-- patterns
--   | pattern patterns
--   | empty
-- tuplepat0
--   | >
--   | pattern tuplepat1
-- tuplepat1
--   | >
--   | , pattern tuplepat1

data Module = Module
  { exports :: !(UnliftedArray ShortText)
  , imports :: !(SmallArray ImportStatement)
  , types :: !(SmallArray TypeDeclaration)
  , terms :: !(SmallArray TermDeclaration)
  } deriving (Show)

data ImportStatement = ImportStatement
  { module_ :: !ShortText
  , imports :: !(SmallArray Import)
  } deriving (Show)

data Import
  = ImportInfix !ShortText
  | ImportType !ShortText
  | ImportTerm !ShortText
  deriving (Show)

data TermDeclaration = TermDeclaration
  { name :: !ShortText
  , type_ :: !TypeScheme
  , definition :: !Term
  } deriving (Show)

data TypeDeclaration = TypeDeclaration
  { name :: !ShortText
  , kind :: !Kind
  -- , classification :: !TypeClassification
  , constructors :: !(SmallArray ConstructorDeclaration)
  } deriving (Show)

data ConstructorDeclaration = ConstructorDeclaration
  { name :: !ShortText
  , argument :: !ConstructorArgument
  }
  deriving (Show)

data ConstructorArgument
  = ConstructorArgumentNone
  | ConstructorArgumentSome !(Type ImplicitlyKindedVar)
  deriving (Show)

-- data TypeClassification
--   = TypeClassificationConstructor !ImplicitlyKindedVar !Kind
--   | TypeClassificationGround !Kind
--   deriving (Show)



data Term
  = Var !ShortText
  | Lam !ShortText !Term
  | Infixes Term InfixChain
  | Tuple [Term]
  | Case !Term [Alternative]
  | Integer !Int64
  | Let !ShortText !Term !Term
  | Rec !(Type ExplicitlyKindedVar) [JoinPoint] !Term
  | Jump !ShortText !Term
  deriving (Show)

data JoinPoint = JoinPoint
  { name :: !ShortText
  , argument :: !ShortText
  , argumentType :: !(Type ExplicitlyKindedVar)
  , body :: !Term
  } deriving (Show)

data Alternative = Alternative
  { pat :: !Pattern
  , arm :: !Term
  } deriving (Show)

data Pattern
  = PatternVariable !ShortText
  | PatternDeconstruction !Deconstruction
  deriving (Show)

data Deconstruction = Deconstruction
  { constructor :: Constructor
  , bindings :: [Pattern]
  } deriving (Show)

data Constructor
  = CustomConstructor !ShortText
  | TupleConstructor
  deriving (Show)

data TypeScheme
  = TypeSchemeExplicitReps
      ![ShortText] -- representation variables
      !(Type ExplicitlyKindedVar)
  | TypeSchemeImplicitReps !(Type ImplicitlyKindedVar)
  deriving (Show)

data KindScheme = KindScheme
  { variables :: ![ShortText]
  , kind :: !Kind
  }

-- data TypeVars
--   = TypeVarsExplicitReps [ShortText] [TypeVar ExplicitRep] -- type vars must have reps
--   | TypeVarsImplicitReps [TypeVar ImplicitRep] -- type vars may omit reps
--   | TypeVarsNone -- type vars and their reps are all inferred
--   deriving (Show)

-- data TypeVar r = TypeVar
--   !ShortText -- name
--   !r -- representation
--   deriving (Show)

data ExplicitlyKindedVar = ExplicitlyKindedVar
  { name :: !ShortText -- type variable name
  , kind :: !Kind -- user-provided kind
  }
  deriving (Show)

newtype ImplicitlyKindedVar = ImplicitlyKindedVar
  { name :: ShortText -- type variable name
  }
  deriving (Show)

data Kind
  = VarK !ShortText
  | TupleK ![Kind]
  | ConstantK !ShortText
  | AppK !Kind !Kind -- TODO: remove this, I think
  deriving (Show)

-- TODO: Support kind applications. Important for fixed-length
-- arrays and SIMD vector types.
data ExplicitRep
  = ExplicitRepVar !ShortText
  | ExplicitRepConstant !ShortText
  deriving (Show)

data ImplicitRep
  = ImplicitRepUnspecified
  | ImplicitRepConstant !ShortText
  deriving (Show)

data Type a
  = VarT !ShortText
  | AppT !(Type a) !(Type a)
  | Arr !(Type a) !(Type a)
  | Constant !ShortText
  | TupleT ![Type a] 
  | Forall ![a] !(Type a)
  deriving (Show)

data InfixChain
  = InfixChainTerminal
  | InfixChainCons !Op !Term !InfixChain
  deriving (Show)

data Op
  = Application
  | CustomOp !ShortText
  deriving (Show)

mapInfixChain :: (Term -> Term) -> InfixChain -> InfixChain
mapInfixChain _ InfixChainTerminal = InfixChainTerminal
mapInfixChain f (InfixChainCons op t ts) = InfixChainCons op (f t) (mapInfixChain f ts)

decodeDeclaration :: SmallArray Token -> Parser.Result String TermDeclaration
decodeDeclaration = Parser.parseSmallArray declaration

decodeModule :: SmallArray Token -> Parser.Result String Module
decodeModule = Parser.parseSmallArray parserModule

parserModule :: Parser Token String s Module
parserModule = do
  Parser.token "module: expecting module keyword" T.Module
  Parser.any "module: expecting module identifier" >>= \case
    T.IdentUpper name -> do
      Parser.token "module: expecting open paren after module identifier" T.ParenOpen
      exports <- exports0
      Parser.token "module: expecting where keyword" T.Where
      importsBldr <- importStatementsParser =<< Parser.effect Builder.new
      let !imports = Chunks.concat importsBldr
      datatypesBldr <- datatypesParser =<< Parser.effect Builder.new
      let !types = Chunks.concat datatypesBldr
      declsBldr <- declarationsParser =<< Parser.effect Builder.new
      let terms = Chunks.concat declsBldr
      pure Module{exports,imports,types,terms}
    _ -> Parser.fail "module: expecting module identifier"

datatypesParser ::
     Builder s TypeDeclaration
  -> Parser Token String s (Chunks TypeDeclaration)
datatypesParser !bldr0 = Parser.peek "datatypesParser: expecting more" >>= \case
  T.Declare -> Parser.effect (Builder.freeze bldr0)
  _ -> do
    _ <- Parser.any "datatypesParser: impossible"
    typeDecl <- typeDeclarationParser
    bldr1 <- Parser.effect (Builder.push typeDecl bldr0)
    datatypesParser bldr1

typeDeclarationParser :: Parser Token String s TypeDeclaration
typeDeclarationParser = Parser.any "typeDeclarationParser: expecting IdentUpper" >>= \case
  T.IdentUpper name -> Parser.any "typeDeclarationParser: expecting more" >>= \case
    T.Colon -> do
      kind <- kindParser
      Parser.token "typeDeclarationParser: expecting equal" T.Equals
      Parser.token "typeDeclarationParser: expecting open curly" T.CurlyOpen
      !ctorsChunks <- dataConstructorsParser0
      let !constructors = Chunks.concat ctorsChunks
      pure TypeDeclaration{name,kind,constructors}
    _ -> Parser.fail "typeDeclarationParser: expected colon"
  _ -> Parser.fail "typeDeclarationParser: expecting IdentUpper" 

dataConstructorsParser0 :: Parser Token String s (Chunks ConstructorDeclaration)
dataConstructorsParser0 = Parser.any "dataConstructorsParser0: more" >>= \case
  T.CurlyClose -> pure Chunks.ChunksNil
  T.IdentUpper name -> do
    bldr0 <- Parser.effect $ do
      bldr <- Builder.new
      let !ctor = ConstructorDeclaration{name,argument=ConstructorArgumentNone}
      Builder.push ctor bldr
    dataConstructorsParser1 bldr0
  _ -> Parser.fail "dataConstructorsParser0: wanted close curly or ident upper"

dataConstructorsParser1 ::
     Builder s ConstructorDeclaration
  -> Parser Token String s (Chunks ConstructorDeclaration)
dataConstructorsParser1 !bldr0 = Parser.any "dataConstructorsParser1: more" >>= \case
  T.CurlyClose -> do
    Parser.effect (Builder.freeze bldr0)
  T.Semicolon -> do
    name <- variableUpper "dataConstructorsParser0: expecting ident upper"
    let !ctor = ConstructorDeclaration{name,argument=ConstructorArgumentNone}
    bldr1 <- Parser.effect (Builder.push ctor bldr0)
    dataConstructorsParser1 bldr1
  _ -> Parser.fail "dataConstructorsParser1: wanted close curly or ident upper"

exports0 :: Parser Token String s (UnliftedArray ShortText)
exports0 = Parser.trySatisfy (== T.ParenClose) >>= \case
  True -> Parser.effect
    (PM.unsafeNewUnliftedArray 0 >>= PM.unsafeFreezeUnliftedArray)
  False -> Parser.sepBy1
    (Parser.any "exports1: expecting comma or close paren" >>= \case
      T.Comma -> pure True
      T.ParenClose -> pure False
      _ -> Parser.fail "exports1: expecting comma or close paren"
    )
    (variable "exports1: expecting identifier after comma")

importStatementsParser ::
     Builder s ImportStatement
  -> Parser Token [Char] s (Chunks ImportStatement)
importStatementsParser !bldr0 = Parser.peek "importStatementsParser: expecting more tokens" >>= \case
  T.Declare -> Parser.effect (Builder.freeze bldr0)
  T.Type -> Parser.effect (Builder.freeze bldr0)
  _ -> do
    impStmt <- importStatementParser
    bldr1 <- Parser.effect (Builder.push impStmt bldr0)
    importStatementsParser bldr1

importStatementParser :: Parser Token [Char] s ImportStatement
importStatementParser = Parser.any "importStatementParser: expecting IdentUpper" >>= \case
  T.IdentUpper module_ -> do
    Parser.token "importStatementParser: expecting open paren" T.ParenOpen
    !imports <- importsParser
    pure ImportStatement{module_,imports}
  _ -> Parser.fail "importStatementParser: expecting IdentUpper" 

importsParser :: Parser Token [Char] s (SmallArray Import)
importsParser = Parser.sepBy1
  (Parser.any "importsParser: expecting comma or close paren" >>= \case
     T.Comma -> pure True
     T.ParenClose -> pure False
     _ -> Parser.fail "importsParser: expecting comma or close paren"
  ) importParser

importParser :: Parser Token [Char] s Import
importParser = Parser.any "importParser: expecting an importable identifier" >>= \case
  T.Infix t -> pure (ImportInfix t)
  T.IdentUpper t -> pure (ImportType t)
  T.IdentLower t -> pure (ImportTerm t)
  _ -> Parser.fail "importParser: expecting an importable identifier" 

declarationsParser ::
     Builder s TermDeclaration
  -> Parser Token String s (Chunks TermDeclaration)
declarationsParser !bldr0 = Parser.isEndOfInput >>= \case
  True -> Parser.effect (Builder.freeze bldr0)
  False -> do
    decl <- declaration
    bldr1 <- Parser.effect (Builder.push decl bldr0)
    declarationsParser bldr1

declaration :: Parser Token String s TermDeclaration
declaration = do
  Parser.any "declaration: expecting declare keyword but got eof" >>= \case
    T.Declare -> pure ()
    t -> Parser.fail ("declaration: expecting declare keyword but got " ++ show t)
  Parser.any "declaration: expecting name" >>= \case
    T.IdentLower name -> do
      Parser.token "declaration: expecting colon" T.Colon
      type_ <- typeScheme
      Parser.token "declaration: expecting as keyword" T.As
      definition <- termchain0
      Parser.any "declaration: got eof when end was expected" >>= \case
        T.End -> pure ()
        token -> Parser.fail ("declaration: expected end, got " ++ show token)
      pure (TermDeclaration{name,type_,definition})
    _ -> Parser.fail "declaration: expecting identifier" 

typeScheme :: Parser Token String s TypeScheme
typeScheme = Parser.peek "typeScheme: expected leading token" >>= \case
  T.Repvar -> do
    _ <- Parser.any "typeScheme: not possible"
    reps <- repvars
    type_ <- typechain0
    pure (TypeSchemeExplicitReps reps type_)
  _ -> do
    type_ <- typechain0
    pure (TypeSchemeExplicitReps [] type_)

tyvarsParser :: HasTyVarParser a => Parser Token String s [a]
tyvarsParser = Parser.peek "tyvarsExplicit: expected leading token" >>= \case
  T.Period -> do
    _ <- Parser.any "tyvarsExplicit: impossible"
    pure []
  _ -> do
    v <- tyVarParser
    vs <- tyvarsParser
    pure (v : vs)

repvars :: Parser Token String s [ShortText]
repvars = do
  rs <- Parser.foldUntil (== T.Period)
    ( \idents -> Parser.any "repvars: expected rep identifier" >>= \case
      T.IdentRep ident -> pure (ident : idents)
      _ -> Parser.fail "repvars: expected rep identifier"
    ) []
  Parser.token "repvars: expected period after identifiers" T.Period
  pure $! List.reverse rs

typechain0 :: HasTyVarParser a => Parser Token String s (Type a)
typechain0 = Parser.peek "typechain0: expected more tokens" >>= \case
  T.Forall -> do
    _ <- Parser.any "typechain0: not possible"
    vs <- tyvarsParser
    t0 <- typeParser
    r <- typechain1 t0
    pure (Forall vs r)
  _ -> do
    t0 <- typeParser
    typechain1 t0

typechain1 :: HasTyVarParser a => Type a -> Parser Token String s (Type a)
typechain1 !acc = Parser.peek "typechain1: expected leading token" >>= \case
  T.Arrow -> do
    _ <- Parser.any "typechain1: not possible"
    t <- typeParser
    t' <- typechain1 t
    pure (Arr acc t')
  _ -> pure acc

tuple0 :: Parser Token String s [Term]
tuple0 = Parser.peek "tuple0: expected leading token" >>= \case
  T.AngleClose -> do
    _ <- Parser.any "tuple0: not possible"
    pure []
  _ -> do
    t <- termchain0
    ts <- tuple1
    pure (t : ts)

tuple1 :: Parser Token String s [Term]
tuple1 = Parser.any "tuple1: expected leading token" >>= \case
  T.AngleClose -> pure []
  T.Comma -> do
    t <- termchain0
    ts <- tuple1
    pure (t : ts)
  _ -> Parser.fail "tuple1: expected angle-close or comma"

typetuple0 :: HasTyVarParser a => Parser Token String s [Type a]
typetuple0 = Parser.peek "typetuple0: expected leading token" >>= \case
  T.AngleClose -> do
    _ <- Parser.any "typetuple0: not possible"
    pure []
  _ -> do
    t <- typechain0
    ts <- typetuple1
    pure (t : ts)

typetuple1 :: HasTyVarParser a => Parser Token String s [Type a]
typetuple1 = Parser.any "typetuple1: expected leading token" >>= \case
  T.AngleClose -> pure []
  T.Comma -> do
    t <- typechain0
    ts <- typetuple1
    pure (t : ts)
  _ -> Parser.fail "typetuple1: expected angle-close or comma"

-- types0 :: Parser Token String s Type
-- types0 = do
--   t <- typeParser
--   ts <- types1
--   pure (AppT (t : ts))
-- 
-- -- Looks to see if the preceeding types is applied to a type argument.
-- types1 :: Parser Token String s (Maybe Type)
-- types1 = Parser.peek "types1: expected leading token" >>= \case
--   T.ParenOpen -> liftA2 (:) typeParser types1
--   T.AngleOpen -> liftA2 (:) typeParser types1
--   T.IdentUpper{} -> liftA2 (:) typeParser types1
--   T.IdentLower{} -> liftA2 (:) typeParser types1
--   _ -> pure []

typeParser :: HasTyVarParser a => Parser Token String s (Type a)
typeParser = Parser.any "typeParser: expected leading token" >>= \case
  T.AngleOpen -> fmap TupleT typetuple0
  T.ParenOpen -> do
    r <- typechain0
    Parser.any "typeParser: expecting close paren" >>= \case
      T.ParenClose -> pure r
      _ -> Parser.fail "typeParser: expecting close paren" 
  T.IdentUpper ident -> do
    Parser.peek "typeParser: peeking for type application" >>= \case
      T.AngleOpen -> do {arg <- typeParser; pure (AppT (Constant ident) arg)}
      T.ParenOpen -> do {arg <- typeParser; pure (AppT (Constant ident) arg)}
      T.IdentUpper{} -> do {arg <- typeParser; pure (AppT (Constant ident) arg)}
      T.IdentLower{} -> do {arg <- typeParser; pure (AppT (Constant ident) arg)}
      _ -> pure $ Constant ident
  T.IdentLower ident -> pure $ VarT ident
  _ -> Parser.fail "typeParser: unexpected token"

term :: Parser Token String s Term
term = Parser.any "term: expected leading token" >>= \case
  T.ParenOpen -> do
    r <- termchain0
    Parser.any "term: expecting close paren" >>= \case
      T.ParenClose -> pure r
      _ -> Parser.fail "term: expecting close paren" 
  T.IdentLower ident -> pure $ Var ident
  T.Integer i -> pure $ Integer i
  T.JumpTo target -> do
    arg <- term -- variable "term: jump requires argument"
    pure $! Jump target arg
  T.Backslash -> Parser.any "term: expecting identifier after lambda" >>= \case
    T.IdentLower ident -> do
      Parser.token "term: expecting arrow after lambda" T.Arrow
      t <- termchain0
      pure (Lam ident t)
    _ -> Parser.fail "term: expecting identifier after lambda" 
  T.AngleOpen -> Tuple <$> tuple0
  T.Case -> do
    expr <- termchain0
    Parser.token "term: expecting of keyword" T.Of
    Parser.token "term: expecting open curly after case-of" T.CurlyOpen
    xs <- alts0
    pure (Case expr xs)
  T.Let -> Parser.any "term: expecting identifier after let" >>= \case
    T.IdentLower ident -> do
      Parser.token "term: expecting equals symbol after let" T.Equals
      boundExpr <- termchain0
      Parser.token "term: expecting in keyword after bound expression" T.In
      inExpr <- termchain0
      pure (Let ident boundExpr inExpr)
    _ -> Parser.fail "term: expecting identifier after let" 
  T.Rec -> do
    resultType <- typechain0
    Parser.token "term: expecting as after rec return type" T.As
    Parser.token "term: expecting open curly brace after rec keyword" T.CurlyOpen
    x0 <- label0
    xs <- labels1
    Parser.token "term: expecting in keyword rec block" T.In
    inExpr <- termchain0
    pure (Rec resultType (x0 : xs) inExpr)
  token -> Parser.fail ("term: unexpected token: " ++ show token)

termchain0 :: Parser Token String s Term
termchain0 = do
  t <- term
  ts <- termchain1
  pure (Infixes t ts)

termchain1 :: Parser Token String s InfixChain
termchain1 = Parser.peek "termchain1: expected leading token" >>= \case
  T.Infix op -> do
    _ <- Parser.any "termchain1: not possible"
    t <- term
    ts <- termchain1
    pure (InfixChainCons (CustomOp op) t ts)
  T.IdentLower{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Integer{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Text{} -> liftA2 (InfixChainCons Application) term termchain1
  T.ParenOpen{} -> liftA2 (InfixChainCons Application) term termchain1
  T.AngleOpen{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Case{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Backslash{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Rec{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Let{} -> liftA2 (InfixChainCons Application) term termchain1
  _ -> pure InfixChainTerminal

alts0 :: Parser Token String s [Alternative]
alts0 = Parser.peek "alts0: expected leading token" >>= \case
  T.CurlyClose -> do
    _ <- Parser.any "alts0: not possible"
    pure []
  _ -> do
    t <- alt
    ts <- alts1
    pure (t : ts)

alts1 :: Parser Token String s [Alternative]
alts1 = Parser.any "alts1: expected leading token" >>= \case
  T.CurlyClose -> pure []
  T.Semicolon -> do
    t <- alt
    ts <- alts1
    pure (t : ts)
  token -> Parser.fail ("alts1: expected curly-close or semicolon, got " ++ show token)

alt :: Parser Token String s Alternative
alt = do
  pat <- patParser
  Parser.token "alt: expecting arrow after pattern" T.Arrow
  arm <- termchain0
  pure Alternative{pat,arm}

patParser :: Parser Token String s Pattern
patParser = Parser.any "patParser: expected token" >>= \case
  T.AngleOpen -> do
    pats <- tuplePat0
    pure (PatternDeconstruction (Deconstruction TupleConstructor pats))
  T.IdentUpper datacon -> do
    pats <- patterns
    pure (PatternDeconstruction (Deconstruction (CustomConstructor datacon) pats))
  T.IdentLower var -> pure (PatternVariable var)
  T.ParenOpen -> patParser <* Parser.token "patParser: expecting close paren" T.ParenClose
  _ -> Parser.fail "patParser: wrong token type"

patterns :: Parser Token String s [Pattern]
patterns = Parser.peek "patterns: expected leading token" >>= \case
  T.ParenOpen -> liftA2 (:) patParser patterns
  T.AngleOpen -> liftA2 (:) patParser patterns
  T.IdentUpper{} -> liftA2 (:) patParser patterns
  T.IdentLower{} -> liftA2 (:) patParser patterns
  _ -> pure []

tuplePat0 :: Parser Token String s [Pattern]
tuplePat0 = Parser.peek "tuplePat0: expected leading token" >>= \case
  T.AngleClose -> do
    _ <- Parser.any "tuplePat0: not possible"
    pure []
  _ -> do
    t <- patParser
    ts <- tuplePat1
    pure (t : ts)

tuplePat1 :: Parser Token String s [Pattern]
tuplePat1 = Parser.any "tuplePat1: expected leading token" >>= \case
  T.AngleClose -> pure []
  T.Comma -> do
    t <- patParser
    ts <- tuplePat1
    pure (t : ts)
  _ -> Parser.fail "tuplePat1: expected angle-close or comma"

variable :: String -> Parser Token String s ShortText
variable e = Parser.any e >>= \case
  T.IdentLower t -> pure t
  _ -> Parser.fail e

variableUpper :: String -> Parser Token String s ShortText
variableUpper e = Parser.any e >>= \case
  T.IdentUpper t -> pure t
  _ -> Parser.fail e

label0 :: Parser Token String s JoinPoint
label0 = do
  Parser.token "label0: expecting label" T.JoinPoint
  name <- variable "label0: expecting name"
  Parser.token "label0: expecting open paren" T.ParenOpen
  argument <- variable "label0: expecting argument"
  Parser.token "label0: expecting colon" T.Colon
  argumentType <- typechain0
  Parser.token "label0: expecting close paren" T.ParenClose
  Parser.token "label0: expecting equals symbol" T.Equals
  body <- termchain0
  pure JoinPoint{name,argument,argumentType,body}

labels1 :: Parser Token String s [JoinPoint]
labels1 = Parser.any "labels1: expected leading token" >>= \case
  T.CurlyClose -> pure []
  T.Semicolon -> do
    t <- label0
    ts <- labels1
    pure (t : ts)
  token -> Parser.fail ("labels1: expected curly-close or semicolon, got " ++ show token)

explicitlyKindedVarParser :: Parser Token String s ExplicitlyKindedVar
explicitlyKindedVarParser = do
  Parser.token "explicitlyKindedVarParser: expected open paren" T.ParenOpen
  name <- variable "explicitlyKindedVarParser: variable identifier required after open paren"
  Parser.token "explicitlyKindedVarParser: expected colon" T.Colon
  kind <- kindParser
  Parser.token "explicitlyKindedVarParser: expected close paren" T.ParenClose
  pure ExplicitlyKindedVar{name,kind}

implicitlyKindedVarParser :: Parser Token String s ImplicitlyKindedVar
implicitlyKindedVarParser = do
  name <- variable "implicitlyKindedVarParser: variable identifier required after open paren"
  pure ImplicitlyKindedVar{name}
  
kindParser :: Parser Token String s Kind
kindParser = Parser.any "kindParser: expecting more tokens" >>= \case
  T.IdentRep v -> pure (VarK v)
  T.IdentUpper v -> pure (ConstantK v)
  _ -> Parser.fail "kindParser: expecting rep var"

class HasTyVarParser a where
  tyVarParser :: Parser Token String s a

instance HasTyVarParser ExplicitlyKindedVar where
  tyVarParser = explicitlyKindedVarParser

instance HasTyVarParser ImplicitlyKindedVar where
  tyVarParser = implicitlyKindedVarParser
