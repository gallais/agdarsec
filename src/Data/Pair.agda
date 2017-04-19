module Data.Pair where

open import Level

record Pair {ℓ ℓ′ : Level} (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field  fst : A
         snd : B
open Pair public

{-# HASKELL type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILED_DATA Pair MAlonzo.Code.Data.Pair.AgdaPair (,) #-}
