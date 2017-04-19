module Data.List.Sized where

open import Level using (Level)
open import Data.Unit
open import Data.Empty
open import Data.Product using (_,_)
open import Data.Nat.Base
open import Data.List.Base as List hiding ([_] ; map)
open import Relation.Unary.Indexed

module _ {ℓ : Level} {A : Set ℓ} where

 ∣_∣≡_ : List A → ℕ → Set
 ∣ []     ∣≡ zero  = ⊤
 ∣ x ∷ xs ∣≡ suc n = ∣ xs ∣≡ n
 ∣ []     ∣≡ suc n = ⊥
 ∣ x ∷ xs ∣≡ zero  = ⊥

module _ {ℓ : Level} where

 record ∣List_∣≡_ (A : Set ℓ) (n : ℕ) : Set ℓ where
   constructor mkSizedList
   field list   : List A
         .proof : ∣ list ∣≡ n
 open ∣List_∣≡_ public

 data View (A : Set ℓ) : (n : ℕ) → ∣List A ∣≡ n → Set ℓ where
   []  : View A 0 (mkSizedList [] _)
   _∷_ : ∀ {n} a (as : ∣List A ∣≡ n) .{e} → View A (suc n) (mkSizedList (a ∷ list as) e)

module _ {ℓ : Level} {A : Set ℓ} where

 trivial : (xs : List A) → ∣ xs ∣≡ length xs
 trivial []       = tt
 trivial (x ∷ xs) = trivial xs

 fromList : (xs : List A) →  ∣List A ∣≡ length xs
 fromList xs = mkSizedList xs (trivial xs)

 view : ∀ {n} (xs : ∣List A ∣≡ n) → View A n xs
 view {zero}  (mkSizedList [] _) = []
 view {suc n} (mkSizedList (x ∷ xs) prf) = x ∷ mkSizedList xs prf
 view {zero}  (mkSizedList (_ ∷ _) ())
 view {suc n} (mkSizedList [] ())

module _ {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} where

 size-map : (f : A → B) (xs : List A) → [ ∣ xs ∣≡_ ⟶ ∣ List.map f xs ∣≡_ ]
 size-map f []       {zero}  prf = tt
 size-map f (x ∷ xs) {suc n} prf = size-map f xs prf
 size-map f []       {suc n} ()
 size-map f (x ∷ xs) {zero}  ()

 map : (A → B) → [ ∣List A ∣≡_ ⟶ ∣List B ∣≡_ ]
 map f (mkSizedList xs prf) = mkSizedList (List.map f xs) (size-map f xs prf)

open import Data.List.Sized.Interface

instance

  sized : ∀ {ℓ} {A : Set ℓ} → Sized A (∣List A ∣≡_)
  Sized.view sized xs with view xs
  Sized.view sized (mkSizedList _ _) | []      = Level.lift tt
  Sized.view sized (mkSizedList _ _) | a ∷ as  = a , as
