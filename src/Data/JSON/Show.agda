{-# OPTIONS --without-K --safe #-}

module Data.JSON.Show where

open import Data.Bool.Base using (false; true)
open import Data.Float.Base using (Float) renaming (show to showꟳ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)
open import Data.JSON
open import Data.JSON.Show.Escape using (escape)

showᴬ : List JSON → String
showᴺⱽ : String × JSON → String
showᴼ : List (String × JSON) → String
show : JSON → String

showᴬ [] = ""
showᴬ (a ∷ []) = show a
showᴬ (a₁ ∷ a₂ ∷ as) = show a₁ ++ ", " ++ showᴬ (a₂ ∷ as)

showᴺⱽ (n , v) = show (string n) ++ ": " ++ show v

showᴼ [] = ""
showᴼ (nv ∷ []) = showᴺⱽ nv
showᴼ (nv₁ ∷ nv₂ ∷ nvs) = showᴺⱽ nv₁ ++ ", " ++ showᴼ (nv₂ ∷ nvs)

show null = "null"
show (bool false) = "false"
show (bool true) = "true"
show (number f) = showꟳ f
show (string s) = "\"" ++ escape s ++ "\""
show (array as) = "[" ++ showᴬ as ++ "]"
show (object o) = "{" ++ showᴼ o ++ "}"

-- Test.
private
  open import Data.Float.Base using (fromRatio) renaming (fromℕ to fromℕꟳ)
  open import Data.Integer.Base using (+_)
  open import Data.List using ([_])
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  _ : show (object [ "name" , (array ((number (fromℕꟳ 1)) ∷ (number (fromRatio (+ 3) (+ 2))) ∷ [])) ])
    ≡ "{\"name\": [1.0, 1.5]}"
  _ = refl
