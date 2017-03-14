module Text.Parser.Combinators where

open import Relation.Unary.Indexed
open import Induction.Nat.Strong as Iℕ hiding (lower)
open import Data.Nat.Base
open import Data.Nat.LTE

open import Data.Sum as S
open import Data.Product as P hiding (,_)
open import Data.Maybe.Base
open import Data.Char
open import Data.Bool.Base
open import Data.Nat.Properties
open import Data.List.Base as List hiding ([_] ; any)
open import Data.List.NonEmpty as NonEmpty using (List⁺ ; _∷⁺_ ; _∷_)
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Agda.Builtin.Equality
import Data.String as String
open String using () renaming (String to Text)

open import Category.Monad
open import Data.List.Sized
open import Text.Parser.Success as Success
open import Function

record Parser (Tok : Set) (M : Set → Set) (A : Set) (n : ℕ) : Set where
  constructor mkParser
  field runParser : ∀ {m} → .(m ≤ n) → ∣List Tok ∣≡ m → M (Success Tok A m)
open Parser public

module _ {Tok : Set} {M : Set → Set} {{𝕄 : RawMonadPlus M}} where

 private module 𝕄 = RawMonadPlus 𝕄

 anyTok : [ Parser Tok M Tok ]

 runParser anyTok lt s with view s
 ... | []     = 𝕄.∅ 
 ... | a ∷ as = 𝕄.return (a ^ ≤-refl , as)

 module _ {A : Set} where

  return : [ Parser Tok M A ⟶ □ Parser Tok M A ]
  runParser (call (return A) m<n) p≤m = runParser A (≤-trans p≤m (<⇒≤ m<n))

  lower : {m n : ℕ} → .(m ≤ n) → Parser Tok M A n → Parser Tok M A m
  runParser (lower m≤n A) p≤m = runParser A (≤-trans p≤m m≤n)

  guard : (A → Bool) → [ Parser Tok M A ⟶ Parser Tok M A ]
  runParser (guard p A) m≤n s =
    runParser A m≤n s 𝕄.>>= λ a →
    if p (Success.value a) then 𝕄.return a else 𝕄.∅

  fail : [ Parser Tok M A ]
  runParser fail _ _ = 𝕄.∅

  infixr 3 _<|>_
  _<|>_ : [ Parser Tok M A ⟶ Parser Tok M A ⟶ Parser Tok M A ]
  runParser (A₁ <|> A₂) m≤n s = runParser A₁ m≤n s 𝕄.∣ runParser A₂ m≤n s

 module _ {A B : Set} where

  infixr 5 _<$>_
  _<$>_ : (A → B) → [ Parser Tok M A ⟶ Parser Tok M B ]
  runParser (f <$> p) lt s = Success.map f 𝕄.<$> (runParser p lt s)

  infixr 5 _<$_
  _<$_ : B → [ Parser Tok M A ⟶ Parser Tok M B ]
  b <$ p = const b <$> p

  _&?>>=_ : [ Parser Tok M A ⟶ (const A ⟶ □ Parser Tok M B) ⟶
              Parser Tok M (A × Maybe B) ]
  runParser (A &?>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (lift (<⇒≤ p<m) (Success.map ((a ,_) ∘ just) rB)))
    𝕄.∣ 𝕄.return (a , nothing ^ p<m , s′)

  _&>>=_ : [ Parser Tok M A ⟶ (const A ⟶ □ Parser Tok M B) ⟶ Parser Tok M (A × B) ]
  runParser (A &>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (lift (<⇒≤ p<m) (Success.map (a ,_) rB)))

 module _ {A B : Set} where

  _>>=_ : [ Parser Tok M A ⟶ (const A ⟶ □ Parser Tok M B) ⟶ Parser Tok M B ]
  A >>= B = proj₂ <$> A &>>= B

  infixl 4 _<&>_ _<&_ _&>_
  _<&>_ : [ Parser Tok M A ⟶ □ Parser Tok M B ⟶ Parser Tok M (A × B) ]
  A <&> B = A &>>= const B

  _<&_ : [ Parser Tok M A ⟶ □ Parser Tok M B ⟶ Parser Tok M A ]
  A <& B = proj₁ <$> (A <&> B)

  _&>_ : [ Parser Tok M A ⟶ □ Parser Tok M B ⟶ Parser Tok M B ]
  A &> B = proj₂ <$> (A <&> B)

 module _ {A B : Set} where

  infixr 5 _<*>_
  _<*>_ : [ Parser Tok M (A → B) ⟶ Parser Tok M A ⟶ Parser Tok M B ]
  F <*> A = uncurry _$_ <$> (F <&> return A)

 module _ {A B : Set} where

  infixl 4 _<&?>_ _<&?_ _&?>_
  _<&?>_ : [ Parser Tok M A ⟶ □ Parser Tok M B ⟶ Parser Tok M (A × Maybe B) ]
  A <&?> B = A &?>>= const B

  _<&?_ : [ Parser Tok M A ⟶ □ Parser Tok M B ⟶ Parser Tok M A ]
  A <&? B = proj₁ <$> (A <&?> B)

  _&?>_ : [ Parser Tok M A ⟶ □ Parser Tok M B ⟶ Parser Tok M (Maybe B) ]
  A &?> B = proj₂ <$> (A <&?> B)

  infixr 3 _<⊎>_
  _<⊎>_ : [ Parser Tok M A ⟶ Parser Tok M B ⟶ Parser Tok M (A ⊎ B) ]
  A <⊎> B = inj₁ <$> A <|> inj₂ <$> B

  infixl 4 _<?&>_ _<?&_ _?&>_
  _<?&>_ : [ Parser Tok M A ⟶ Parser Tok M B ⟶ Parser Tok M (Maybe A × B) ]
  runParser (A <?&> B) m≤n s =
    (runParser (A <⊎> B) m≤n s) 𝕄.>>= λ rA⊎B → let (a⊎b ^ p<m , s′) = rA⊎B in
    case a⊎b of λ where
      (inj₂ b) → 𝕄.return (nothing , b ^ p<m , s′)
      (inj₁ a) → let r = runParser ((just a ,_) <$> B) (≤-trans (<⇒≤ p<m) m≤n) s′
                 in lift (<⇒≤ p<m) 𝕄.<$> r

  _<?&_ : [ Parser Tok M A ⟶ Parser Tok M B ⟶ Parser Tok M (Maybe A) ]
  A <?& B = proj₁ <$> (A <?&> B)

  _?&>_ : [ Parser Tok M A ⟶ Parser Tok M B ⟶ Parser Tok M B ]
  A ?&> B = proj₂ <$> (A <?&> B)

 module _ {A B C : Set} where

  between : [ Parser Tok M A ⟶ □ Parser Tok M C ⟶ □ Parser Tok M B ⟶ Parser Tok M B ]
  between A C B = A &> B <& C

 module _ {{eq? : Decidable {A = Tok} _≡_}} where

  anyOf : List Tok → [ Parser Tok M Tok ]
  anyOf ts = guard (λ c → not (null ts) ∧ List.any (⌊_⌋ ∘ eq? c) ts) anyTok

  exact : Tok → [ Parser Tok M Tok ]
  exact = anyOf ∘ List.[_]

  exacts : List⁺ Tok → [ Parser Tok M (List⁺ Tok) ]
  exacts (x ∷ xs) = go x xs where

    go : Tok → List Tok → [ Parser Tok M (List⁺ Tok) ]
    go x []       = NonEmpty.[_] <$> exact x
    go x (y ∷ xs) = uncurry _∷⁺_ <$> (exact x <&> return (go y xs))

 module _ {A : Set} where

  schainl : [ Success Tok A ⟶ □ Parser Tok M (A → A) ⟶ M ∘ Success Tok A ]
  schainl = fix goal $ λ rec sA op → rest rec sA op 𝕄.∣ 𝕄.return sA where

    goal = Success Tok A ⟶ □ Parser Tok M (A → A) ⟶ M ∘ Success Tok A

    rest : [ □ goal ⟶ goal ]
    rest rec (a ^ p<m , s) op = runParser (call op p<m) ≤-refl s 𝕄.>>= λ sOp →
          call rec p<m (Success.map (_$ a) sOp) (Iℕ.lower (<⇒≤ p<m) op) 𝕄.>>=
          𝕄.return ∘ lift (<⇒≤ p<m)

  iterate : [ Parser Tok M A ⟶ □ Parser Tok M (A → A) ⟶ Parser Tok M A ]
  runParser (iterate {n} a op) m≤n s =
    runParser a m≤n s 𝕄.>>= λ sA → schainl sA $ Iℕ.lower m≤n op

 module _ {A B : Set} where

  hchainl : [ Parser Tok M A ⟶ □ Parser Tok M (A → B → A) ⟶ □ Parser Tok M B ⟶
              Parser Tok M A ]
  hchainl A op B = iterate A (map2 (_<*>_ ∘ (flip <$>_)) op B)

 module _ {A : Set} where

  chainl1 : [ Parser Tok M A ⟶ □ Parser Tok M (A → A → A) ⟶ Parser Tok M A ]
  chainl1 a op = hchainl a op (return a)

  chainr1 : [ Parser Tok M A ⟶ □ Parser Tok M (A → A → A) ⟶ Parser Tok M A ]
  chainr1 = fix goal $ λ rec A op → mkParser λ m≤n s →
            runParser A m≤n s 𝕄.>>= λ sA → 
            rest (Iℕ.lower m≤n rec) (lower m≤n A) (Iℕ.lower m≤n op) sA
            𝕄.∣  𝕄.return sA where

    goal = Parser Tok M A ⟶ □ Parser Tok M (A → A → A) ⟶ Parser Tok M A

    rest : [ □ goal ⟶ Parser Tok M A ⟶ □ Parser Tok M (A → A → A) ⟶
             Success Tok A ⟶ M ∘ Success Tok A ]
    rest rec A op sA@(a ^ m<n , s) = runParser (call op m<n) ≤-refl s 𝕄.>>=
          λ sOp → let (f ^ p<m , s′) = sOp ; .p<n : _ < _; p<n = <-trans p<m m<n in
          let rec′ = call rec p<n (lower (<⇒≤ p<n) A) (Iℕ.lower (<⇒≤ p<n) op) in
          lift (<⇒≤ p<n) ∘ Success.map (f a $_) 𝕄.<$> runParser rec′ ≤-refl s′

  head+tail : [ Parser Tok M A ⟶ □ Parser Tok M A ⟶ Parser Tok M (List⁺ A) ]
  head+tail hd tl = NonEmpty.reverse
                <$> (iterate (NonEmpty.[_] <$> hd) (Iℕ.map (NonEmpty._∷⁺_ <$>_) tl))

  list⁺ : [ Parser Tok M A ⟶ Parser Tok M (List⁺ A) ]
  list⁺ pA = head+tail pA (return pA)
