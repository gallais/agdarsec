module Text.Parser.Combinators where

open import Relation.Unary.Indexed
open import Induction.Nat.Strong as Box hiding (≤-lower ; <-lower)
open import Data.Nat.Base hiding (_^_)

open import Data.Sum as Sum
open import Data.Product as Prod hiding (,_)
open import Data.Maybe.Base
open import Data.Char
open import Data.Bool.Base
open import Data.Nat.Properties
open import Data.List.Base as List hiding ([_] ; any)
open import Data.List.NonEmpty as NonEmpty using (List⁺ ; _∷⁺_ ; _∷_)
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Decidable
import Data.String as String
open String using () renaming (String to Text)

open import Category.Monad
open import Data.List.Sized.Interface

open import Function

open import Text.Parser.Types
open import Text.Parser.Success as S hiding (guardM)

module _ {P : Parameters}
         {{𝕊 : Sized (Parameters.Tok P) (Parameters.Toks P)}}
         {{𝕄 : RawMonadPlus (Parameters.M P)}}
         where

 private module 𝕄 = RawMonadPlus 𝕄
 private module P = Parameters P

 anyTok : [ Parser P P.Tok ]
 runParser anyTok m≤n s = case view s of λ where
   nothing  → 𝕄.∅
   (just t) → P.recordToken (Success.value t) 𝕄.>> 𝕄.return t

 module _ {A B : Set} where

  guardM : (A → Maybe B) → [ Parser P A ⟶ Parser P B ]
  runParser (guardM p A) m≤n s =
    runParser A m≤n s 𝕄.>>= maybe 𝕄.return 𝕄.∅ ∘ S.guardM p

 module _ {A : Set} where

  guard : (A → Bool) → [ Parser P A ⟶ Parser P A ]
  guard p = guardM (λ a → if p a then just a else nothing)

  maybeTok : (P.Tok → Maybe A) → [ Parser P A ]
  maybeTok p = guardM p anyTok

  ≤-lower : {m n : ℕ} → .(m ≤ n) → Parser P A n → Parser P A m
  runParser (≤-lower m≤n A) p≤m = runParser A (≤-trans p≤m m≤n)

  <-lower : {m n : ℕ} → .(m < n) → Parser P A n → Parser P A m
  <-lower m<n = ≤-lower (<⇒≤ m<n)

  box : [ Parser P A ⟶ □ Parser P A ]
  box = ≤-close ≤-lower

  fail : [ Parser P A ]
  runParser fail _ _ = 𝕄.∅

  infixr 3 _<|>_
  _<|>_ : [ Parser P A ⟶ Parser P A ⟶ Parser P A ]
  runParser (A₁ <|> A₂) m≤n s = runParser A₁ m≤n s 𝕄.∣ runParser A₂ m≤n s

 module _ {A B : Set} where

  infixr 5 _<$>_
  _<$>_ : (A → B) → [ Parser P A ⟶ Parser P B ]
  runParser (f <$> p) lt s = S.map f 𝕄.<$> (runParser p lt s)

  infixr 5 _<$_
  _<$_ : B → [ Parser P A ⟶ Parser P B ]
  b <$ p = const b <$> p

  _&?>>=_ : [ Parser P A ⟶ (const A ⟶ □ Parser P B) ⟶
              Parser P (A × Maybe B) ]
  runParser (A &?>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (S.and rA (S.map just rB)))
    𝕄.∣ 𝕄.return (a , nothing ^ p<m , s′)

  _&>>=_ : [ Parser P A ⟶ (const A ⟶ □ Parser P B) ⟶ Parser P (A × B) ]
  runParser (A &>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (S.and rA rB))

 module _ {A B : Set} where

  _>>=_ : [ Parser P A ⟶ (const A ⟶ □ Parser P B) ⟶ Parser P B ]
  A >>= B = proj₂ <$> A &>>= B

  infixl 4 _<&>_ _<&_ _&>_
  _<&>_ : [ Parser P A ⟶ □ Parser P B ⟶ Parser P (A × B) ]
  A <&> B = A &>>= const B

  _<&_ : [ Parser P A ⟶ □ Parser P B ⟶ Parser P A ]
  A <& B = proj₁ <$> (A <&> B)

  _&>_ : [ Parser P A ⟶ □ Parser P B ⟶ Parser P B ]
  A &> B = proj₂ <$> (A <&> B)

 module _ {A : Set} where

  alts : [ List ⊚ Parser P A ⟶ Parser P A ]
  alts = List.foldr _<|>_ fail

  ands : [ List⁺ ⊚ Parser P A ⟶ Parser P (List⁺ A) ]
  ands ps = NonEmpty.foldr₁ (λ p ps → uncurry NonEmpty._⁺++⁺_ <$> (p <&> box ps))
            (NonEmpty.map (NonEmpty.[_] <$>_) ps)

 module _ {A B : Set} where

  infixl 4 _<*>_
  _<*>_ : [ Parser P (A → B) ⟶ □ Parser P A ⟶ Parser P B ]
  F <*> A = uncurry _$_ <$> (F <&> A)

  infixl 4 _<&M>_ _<&M_ _&M>_
  _<&M>_ : [ Parser P A ⟶ κ P.M B ⟶ Parser P (A × B) ]
  runParser (A <&M> B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA → B 𝕄.>>= λ b →
    𝕄.return (S.map (_, b) rA)

  _<&M_ : [ Parser P A ⟶ κ P.M B ⟶ Parser P A ]
  A <&M B = proj₁ <$> (A <&M> B)

  _&M>_ : [ Parser P A ⟶ κ P.M B ⟶ Parser P B ]
  A &M> B = proj₂ <$> (A <&M> B)

  infixl 4 _<&?>_ _<&?_ _&?>_
  _<&?>_ : [ Parser P A ⟶ □ Parser P B ⟶ Parser P (A × Maybe B) ]
  A <&?> B = A &?>>= const B

  _<&?_ : [ Parser P A ⟶ □ Parser P B ⟶ Parser P A ]
  A <&? B = proj₁ <$> (A <&?> B)

  _&?>_ : [ Parser P A ⟶ □ Parser P B ⟶ Parser P (Maybe B) ]
  A &?> B = proj₂ <$> (A <&?> B)

  infixr 3 _<⊎>_
  _<⊎>_ : [ Parser P A ⟶ Parser P B ⟶ Parser P (A ⊎ B) ]
  A <⊎> B = inj₁ <$> A <|> inj₂ <$> B

  infixl 4 _<?&>_ _<?&_ _?&>_
  _<?&>_ : [ Parser P A ⟶ Parser P B ⟶ Parser P (Maybe A × B) ]
  A <?&> B = just <$> A <&> box B <|> (nothing ,_) <$> B

  _<?&_ : [ Parser P A ⟶ Parser P B ⟶ Parser P (Maybe A) ]
  A <?& B = proj₁ <$> (A <?&> B)

  _?&>_ : [ Parser P A ⟶ Parser P B ⟶ Parser P B ]
  A ?&> B = proj₂ <$> (A <?&> B)

  infixl 4 _<M&>_ _<M&_ _M&>_
  _<M&>_ : [ κ P.M A ⟶ Parser P B ⟶ Parser P (A × B) ]
  runParser (A <M&> B) m≤n s =
    A 𝕄.>>= λ a → S.map (a ,_) 𝕄.<$> runParser B m≤n s

  _<M&_ : [ κ P.M A ⟶ Parser P B ⟶ Parser P A ]
  A <M& B = proj₁ <$> (A <M&> B)

  _M&>_ : [ κ P.M A ⟶ Parser P B ⟶ Parser P B ]
  A M&> B = proj₂ <$> (A <M&> B)

 module _ {A B C : Set} where

  between : [ Parser P A ⟶ □ Parser P C ⟶ □ Parser P B ⟶ Parser P B ]
  between A C B = A &> B <& C

  between? : [ Parser P A ⟶ □ Parser P C ⟶ Parser P B ⟶ Parser P B ]
  between? A C B = between A C (box B) <|> B

 module _ {{eq? : DecidableEquality P.Tok}} where

  anyOf : List P.Tok → [ Parser P P.Tok ]
  anyOf ts = guard (λ c → not (null ts) ∧ List.any (⌊_⌋ ∘ decide eq? c) ts) anyTok

  exact : P.Tok → [ Parser P P.Tok ]
  exact = anyOf ∘ List.[_]

  exacts : List⁺ P.Tok → [ Parser P (List⁺ P.Tok) ]
  exacts ts = ands (NonEmpty.map (λ t → exact t) ts)

 module _ {A : Set} where

  schainl : [ Success P.Toks A ⟶ □ Parser P (A → A) ⟶ P.M ∘ Success P.Toks A ]
  schainl = fix goal $ λ rec sA op → rest rec sA op 𝕄.∣ 𝕄.return sA where

    goal = Success P.Toks A ⟶ □ Parser P (A → A) ⟶ P.M ∘ Success P.Toks A

    rest : [ □ goal ⟶ goal ]
    rest rec (a ^ p<m , s) op = runParser (call op p<m) ≤-refl s 𝕄.>>= λ sOp →
          call rec p<m (S.map (_$ a) sOp) (Box.<-lower p<m op) 𝕄.>>=
          𝕄.return ∘ <-lift p<m

  iterate : [ Parser P A ⟶ □ Parser P (A → A) ⟶ Parser P A ]
  runParser (iterate {n} a op) m≤n s =
    runParser a m≤n s 𝕄.>>= λ sA → schainl sA $ Box.≤-lower m≤n op

 module _ {A B : Set} where

  hchainl : [ Parser P A ⟶ □ Parser P (A → B → A) ⟶ □ Parser P B ⟶
              Parser P A ]
  hchainl A op B = iterate A (map2 _<*>_ (Box.map (flip <$>_) op) (duplicate B))

 module _ {A : Set} where

  chainl1 : [ Parser P A ⟶ □ Parser P (A → A → A) ⟶ Parser P A ]
  chainl1 a op = hchainl a op (box a)

  chainr1 : [ Parser P A ⟶ □ Parser P (A → A → A) ⟶ Parser P A ]
  chainr1 = fix goal $ λ rec A op → mkParser λ m≤n s →
            runParser A m≤n s 𝕄.>>= λ sA →
            rest (Box.≤-lower m≤n rec) (≤-lower m≤n A) (Box.≤-lower m≤n op) sA
            𝕄.∣  𝕄.return sA where

    goal = Parser P A ⟶ □ Parser P (A → A → A) ⟶ Parser P A

    rest : [ □ goal ⟶ Parser P A ⟶ □ Parser P (A → A → A) ⟶
             Success P.Toks A ⟶ P.M ∘ Success P.Toks A ]
    rest rec A op sA@(a ^ m<n , s) = runParser (call op m<n) ≤-refl s 𝕄.>>=
          λ sOp → let (f ^ p<m , s′) = sOp ; .p<n : _ < _; p<n = <-trans p<m m<n in
          let rec′ = call rec p<n (<-lower p<n A) (Box.<-lower p<n op) in
          <-lift p<n ∘ S.map (f a $_) 𝕄.<$> runParser rec′ ≤-refl s′

  head+tail : [ Parser P A ⟶ □ Parser P A ⟶ Parser P (List⁺ A) ]
  head+tail hd tl = NonEmpty.reverse
                <$> (iterate (NonEmpty.[_] <$> hd) (Box.map (NonEmpty._∷⁺_ <$>_) tl))

  list⁺ : [ Parser P A ⟶ Parser P (List⁺ A) ]
  list⁺ = fix (Parser P A ⟶ Parser P (List⁺ A)) $ λ rec pA →
          uncurry (λ hd → (hd ∷_) ∘ maybe NonEmpty.toList [])
          <$> (pA <&?> (app rec (box pA)))
