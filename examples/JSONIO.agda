{-# OPTIONS --guardedness #-}

module JSONIO where

open import Data.List.Base using (_∷_; [])
open import Text.Parser.IO using (runParserIO)
open import Text.Parser.JSON using (value)

open import Function.Base using (_$_)

open import IO.Base
open import IO.Finite

open import System.Environment

main : Main
main = run $ do
  (fp ∷ []) ← getArgs
    where _ → putStrLn "Pass a single filepath"
  txt  ← readFile fp
  json ← runParserIO value txt
  putStrLn "Success!"
