{-# OPTIONS --without-K --safe #-}

module Data.JSON where

open import Data.Bool.Base using (Bool)
open import Data.Float.Base using (Float)
open import Data.List.Base using (List)
open import Data.Product using (_×_)
open import Data.String.Base using (String)

-- I wish I could use a sized type here but unfortunately they're not
-- considered safe anymore.
data JSON : Set where
  null   : JSON
  bool   : Bool → JSON
  number : Float → JSON
  string : String → JSON
  array  : List JSON → JSON
  object : List (String × JSON) → JSON
