\begin{code}
module Text.Parser.Combinators where

import Level
open import Relation.Unary.Indexed
open import Induction.Nat.Strong as Iℕ hiding (lower)
open import Data.Nat.Base
open import Data.Nat.LTE

open import Data.Vec hiding ([_] ; map ; _>>=_)
open import Data.Sum as S
open import Data.Product as P hiding (,_)
open import Data.Maybe.Base
open import Data.Char
open import Data.Bool.Base
open import Data.Nat.Properties
open import Data.List as List hiding ([_] ; any)
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
\end{code}
%<*parser>
\begin{code}
record Parser (A : Set) (n : ℕ) : Set where
  constructor mkParser
  field runParser :  ∀ {m} → .(m ≤ n) → Vec Char m →
                     List (Success A m)
\end{code}
%</parser>
\begin{code}
open Parser public

module _ where

 private module 𝕄 = RawMonadPlus (List.monadPlus {Level.zero})

 anyChar : [ Parser Char ]
 runParser anyChar m≤n s with s
 ... | []     = 𝕄.∅
 ... | t ∷ ts = 𝕄.return (t ^ ≤-refl , ts)

 module _ {A B : Set} where

  guardM : (A → Maybe B) → [ Parser A ⟶ Parser B ]
  runParser (guardM p A) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA → let (a ^ p<m , s′) = rA in
    maybe (λ b → 𝕄.return (b ^ p<m , s′)) 𝕄.∅ (p a)

 module _ {A : Set} where

  guard : (A → Bool) → [ Parser A ⟶ Parser A ]
  guard p = guardM (λ a → if p a then just a else nothing)

  maybeChar : (Char → Maybe A) → [ Parser A ]
  maybeChar p = guardM p anyChar

  return : [ Parser A ⟶ □ Parser A ]
  runParser (call (return A) m<n) p≤m = runParser A (≤-trans p≤m (<⇒≤ m<n))

  lower : {m n : ℕ} → .(m ≤ n) → Parser A n → Parser A m
  runParser (lower m≤n A) p≤m = runParser A (≤-trans p≤m m≤n)

  fail : [ Parser A ]
  runParser fail _ _ = 𝕄.∅

  infixr 3 _<|>_
  _<|>_ : [ Parser A ⟶ Parser A ⟶ Parser A ]
  runParser (A₁ <|> A₂) m≤n s = runParser A₁ m≤n s 𝕄.∣ runParser A₂ m≤n s

 module _ {A B : Set} where

  infixr 5 _<$>_
  _<$>_ : (A → B) → [ Parser A ⟶ Parser B ]
  runParser (f <$> p) lt s = Success.map f 𝕄.<$> (runParser p lt s)

  infixr 5 _<$_
  _<$_ : B → [ Parser A ⟶ Parser B ]
  b <$ p = const b <$> p

  _&?>>=_ : [ Parser A ⟶ (const A ⟶ □ Parser B) ⟶
              Parser (A × Maybe B) ]
  runParser (A &?>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (lift (<⇒≤ p<m) (Success.map ((a ,_) ∘ just) rB)))
    𝕄.∣ 𝕄.return (a , nothing ^ p<m , s′)

  _&>>=_ : [ Parser A ⟶ (const A ⟶ □ Parser B) ⟶ Parser (A × B) ]
  runParser (A &>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (lift (<⇒≤ p<m) (Success.map (a ,_) rB)))

 module _ {A B : Set} where

  _>>=_ : [ Parser A ⟶ (const A ⟶ □ Parser B) ⟶ Parser B ]
  A >>= B = proj₂ <$> A &>>= B

  infixl 4 _<&>_ _<&_ _&>_
  _<&>_ : [ Parser A ⟶ □ Parser B ⟶ Parser (A × B) ]
  A <&> B = A &>>= const B

  _<&_ : [ Parser A ⟶ □ Parser B ⟶ Parser A ]
  A <& B = proj₁ <$> (A <&> B)

  _&>_ : [ Parser A ⟶ □ Parser B ⟶ Parser B ]
  A &> B = proj₂ <$> (A <&> B)

 module _ {A B : Set} where

  infixl 4 _<*>_
  _<*>_ : [ Parser (A → B) ⟶ □ Parser A ⟶ Parser B ]
  F <*> A = uncurry _$_ <$> (F <&> A)

  infixl 4 _<&?>_ _<&?_ _&?>_
  _<&?>_ : [ Parser A ⟶ □ Parser B ⟶ Parser (A × Maybe B) ]
  A <&?> B = A &?>>= const B

  _<&?_ : [ Parser A ⟶ □ Parser B ⟶ Parser A ]
  A <&? B = proj₁ <$> (A <&?> B)

  _&?>_ : [ Parser A ⟶ □ Parser B ⟶ Parser (Maybe B) ]
  A &?> B = proj₂ <$> (A <&?> B)

  infixr 3 _<⊎>_
  _<⊎>_ : [ Parser A ⟶ Parser B ⟶ Parser (A ⊎ B) ]
  A <⊎> B = inj₁ <$> A <|> inj₂ <$> B

  infixl 4 _<?&>_ _<?&_ _?&>_
  _<?&>_ : [ Parser A ⟶ Parser B ⟶ Parser (Maybe A × B) ]
  runParser (A <?&> B) m≤n s =
    (runParser (A <⊎> B) m≤n s) 𝕄.>>= λ rA⊎B → let (a⊎b ^ p<m , s′) = rA⊎B in
    case a⊎b of λ where
      (inj₂ b) → 𝕄.return (nothing , b ^ p<m , s′)
      (inj₁ a) → let r = runParser ((just a ,_) <$> B) (≤-trans (<⇒≤ p<m) m≤n) s′
                 in lift (<⇒≤ p<m) 𝕄.<$> r

  _<?&_ : [ Parser A ⟶ Parser B ⟶ Parser (Maybe A) ]
  A <?& B = proj₁ <$> (A <?&> B)

  _?&>_ : [ Parser A ⟶ Parser B ⟶ Parser B ]
  A ?&> B = proj₂ <$> (A <?&> B)

 module _ {A B C : Set} where

  between : [ Parser A ⟶ □ Parser C ⟶ □ Parser B ⟶ Parser B ]
  between A C B = A &> B <& C

  between? : [ Parser A ⟶ □ Parser C ⟶ Parser B ⟶ Parser B ]
  between? A C B = between A C (return B) <|> B

 module _ {{eq? : Decidable {A = Char} _≡_}} where

  anyOf : List Char → [ Parser Char ]
  anyOf ts = guard (λ c → not (null ts) ∧ List.any (⌊_⌋ ∘ eq? c) ts) anyChar

  exact : Char → [ Parser Char ]
  exact = anyOf ∘ List.[_]

  exacts : List⁺ Char → [ Parser (List⁺ Char) ]
  exacts (x ∷ xs) = go x xs where

    go : Char → List Char → [ Parser (List⁺ Char) ]
    go x []       = NonEmpty.[_] <$> exact x
    go x (y ∷ xs) = uncurry _∷⁺_ <$> (exact x <&> return (go y xs))

 module _ {A : Set} where

  schainl : [ Success A ⟶ □ Parser (A → A) ⟶ List ∘ Success A ]
  schainl = fix goal $ λ rec sA op → rest rec sA op 𝕄.∣ 𝕄.return sA where

    goal = Success A ⟶ □ Parser (A → A) ⟶ List ∘ Success A

    rest : [ □ goal ⟶ goal ]
    rest rec (a ^ p<m , s) op = runParser (call op p<m) ≤-refl s 𝕄.>>= λ sOp →
          call rec p<m (Success.map (_$ a) sOp) (Iℕ.lower (<⇒≤ p<m) op) 𝕄.>>=
          𝕄.return ∘ lift (<⇒≤ p<m)

  iterate : [ Parser A ⟶ □ Parser (A → A) ⟶ Parser A ]
  runParser (iterate {n} a op) m≤n s =
    runParser a m≤n s 𝕄.>>= λ sA → schainl sA $ Iℕ.lower m≤n op

 module _ {A B : Set} where

  hchainl : [ Parser A ⟶ □ Parser (A → B → A) ⟶ □ Parser B ⟶
              Parser A ]
  hchainl A op B = iterate A (map2 _<*>_ (Iℕ.map (flip <$>_) op) (duplicate B))

 module _ {A : Set} where

  chainl1 : [ Parser A ⟶ □ Parser (A → A → A) ⟶ Parser A ]
  chainl1 a op = hchainl a op (return a)

  chainr1 : [ Parser A ⟶ □ Parser (A → A → A) ⟶ Parser A ]
  chainr1 = fix goal $ λ rec A op → mkParser λ m≤n s →
            runParser A m≤n s 𝕄.>>= λ sA →
            rest (Iℕ.lower m≤n rec) (lower m≤n A) (Iℕ.lower m≤n op) sA
            𝕄.∣  𝕄.return sA where

    goal = Parser A ⟶ □ Parser (A → A → A) ⟶ Parser A

    rest : [ □ goal ⟶ Parser A ⟶ □ Parser (A → A → A) ⟶
             Success A ⟶ List ∘ Success A ]
    rest rec A op sA@(a ^ m<n , s) = runParser (call op m<n) ≤-refl s 𝕄.>>=
          λ sOp → let (f ^ p<m , s′) = sOp ; .p<n : _ < _; p<n = <-trans p<m m<n in
          let rec′ = call rec p<n (lower (<⇒≤ p<n) A) (Iℕ.lower (<⇒≤ p<n) op) in
          lift (<⇒≤ p<n) ∘ Success.map (f a $_) 𝕄.<$> runParser rec′ ≤-refl s′

  head+tail : [ Parser A ⟶ □ Parser A ⟶ Parser (List⁺ A) ]
  head+tail hd tl = NonEmpty.reverse
                <$> (iterate (NonEmpty.[_] <$> hd) (Iℕ.map (NonEmpty._∷⁺_ <$>_) tl))

  list⁺ : [ Parser A ⟶ Parser (List⁺ A) ]
  list⁺ pA = head+tail pA (return pA)
\end{code}
