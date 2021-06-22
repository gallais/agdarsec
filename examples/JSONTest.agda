{-# OPTIONS --guardedness #-}

module JSONTest where

open import Level using (0ℓ)
open import Data.List.Base using (_∷_; [])
open import Data.JSON
open import Text.Parser 0ℓ
  using (runParserIO; P-monad; P-monad0; P-monad+
        ; vec; decide-char
        ; Subset-refl)
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
