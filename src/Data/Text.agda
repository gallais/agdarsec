module Data.Text where

open import Data.Char.Base
open import Data.String.Base
open import Data.Maybe.Base
open import Data.List.Base hiding (uncons)
open import Data.Pair
open import Relation.Binary.PropositionalEquality

postulate uncons : String → Maybe (Pair Char String)

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC uncons = Data.Text.uncons #-}


postulate
  uncons-list : (s : String) →
                toList s ≡ maybe (λ p → fst p ∷ toList (snd p)) [] (uncons s)
