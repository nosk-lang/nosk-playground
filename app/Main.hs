{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}

module Main where

import Control.Monad (when)
import Data.Parser (Result(..),Slice(..))
import Text.Show.Pretty (pPrint)
import Poly.Typecheck (typecheckDeclaration)

import qualified Data.Primitive as PM
import qualified Poly.Associate as Associate
import qualified Poly.Unchained as Unchained
import qualified Poly.Flattened as Flattened
import qualified Poly.Rename as Rename
import qualified Poly.Syntax as Syntax
import qualified Poly.Token as Token
import qualified Data.Bytes.Chunks as Chunks
import qualified System.IO as IO
import qualified Data.Text.Lazy.IO as T
import qualified Poly.Optimize.DeadCodeElimination as DeadCodeElimination

main :: IO ()
main = do
  c <- Chunks.hGetContents IO.stdin
  case Token.tokenize (Chunks.concat c) of
    Nothing -> fail "bad token stream"
    Just ts -> do
      print ts
      case Syntax.decodeModule ts of
        Success (Slice off len r) -> do
          print r
          case Rename.renameModule r of
            Left e -> fail (show e)
            Right renamed -> do
              putStrLn "After rename"
              print renamed
              case Associate.associateModule renamed of
                Left err -> fail err
                Right t -> do
                  putStrLn "After infix cleanup"
                  pPrint t
                  let flattened = Flattened.flattenModule t
                  putStrLn "After flattening pattern matches"
                  pPrint flattened
                  let Flattened.Module{terms} = flattened
                  when (PM.sizeofSmallArray terms /= 1) (fail "expecting 1 term")
                  let t0 = PM.indexSmallArray terms 0
                  case typecheckDeclaration t0 of
                    Left err -> fail (show err)
                    Right _ -> do
                      putStrLn "Typechecking succeeded"
                      putStrLn "After optimization"
                      pPrint (DeadCodeElimination.termDecl t0)
        Failure err -> fail err

-- optimize :: Module -> Module
-- optimize = DeadCodeElimination.module_
