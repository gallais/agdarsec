{-# OPTIONS --without-K --safe #-}

module Text.Parser.Combinators where

open import Level.Bounded as Level≤ hiding (map)

open import Relation.Unary using (IUniversal; _⇒_)
open import Induction.Nat.Strong as Box using (□_)
open import Data.Nat.Base using (ℕ; _≤_; _<_)


open import Data.Bool.Base as Bool using (Bool; if_then_else_; not; _∧_)
open import Data.List.Base as List using (_∷_; []; null)
open import Data.List.NonEmpty as List⁺ using (_∷⁺_ ; _∷_)
open import Data.Maybe.Base using (just; nothing; maybe)
open import Data.Product as Product using (_,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base as Sum using (inj₁; inj₂)

open import Data.Char as Char using (Char)
open import Data.Nat.Properties as Nat using (≤-refl; ≤-trans; <⇒≤; <-trans)
import Data.List.Relation.Unary.Any as Any
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality.Decidable.Core using (DecidableEquality; decide)
open import Data.String as String using () renaming (String to Text)

open import Category.Monad using (RawMonadPlus)
open import Data.List.Sized.Interface using (Sized)

open import Function

open import Text.Parser.Types
open import Text.Parser.Success as S hiding (guardM)

module _ {l} {P : Parameters l} (open Parameters P)
         {{𝕊 : Sized Tok Toks}} {{𝕄 : RawMonadPlus M}}
         where

 private module 𝕄 = RawMonadPlus 𝕄
 private module P = Parameters P

 anyTok : ∀[ Parser P P.Tok ]
 runParser anyTok m≤n s = case view (lower s) of λ where
   nothing  → 𝕄.∅
   (just t) → t 𝕄.<$ P.recordToken (lower $ Success.value t)

 module _ {A B : Set≤ l} where

  guardM : (theSet A → theSet (Maybe B)) → ∀[ Parser P A ⇒ Parser P B ]
  runParser (guardM p A) m≤n s =
    runParser A m≤n s 𝕄.>>= maybe 𝕄.return 𝕄.∅ ∘ S.guardM p

 module _ {A : Set≤ l} where

  guard : (theSet A → Bool) → ∀[ Parser P A ⇒ Parser P A ]
  guard p = guardM (λ a → if p a then just a else nothing)

  maybeTok : (theSet P.Tok → theSet (Maybe A)) → ∀[ Parser P A ]
  maybeTok p = guardM p anyTok

  ≤-lower : {m n : ℕ} → .(m ≤ n) → Parser P A n → Parser P A m
  runParser (≤-lower m≤n A) p≤m = runParser A (≤-trans p≤m m≤n)

  <-lower : {m n : ℕ} → .(m < n) → Parser P A n → Parser P A m
  <-lower m<n = ≤-lower (<⇒≤ m<n)

  box : ∀[ Parser P A ⇒ □ Parser P A ]
  box = Box.≤-close ≤-lower

  fail : ∀[ Parser P A ]
  runParser fail _ _ = 𝕄.∅

  infixr 3 _<|>_
  _<|>_ : ∀[ Parser P A ⇒ Parser P A ⇒ Parser P A ]
  runParser (A₁ <|> A₂) m≤n s = runParser A₁ m≤n s 𝕄.∣ runParser A₂ m≤n s

 module _ {A B C : Set≤ l} where

  lift2 : ∀[ Parser P A ⇒ Parser P B ⇒ Parser P C ] →
          ∀[ □ (Parser P A) ⇒ □ (Parser P B) ⇒ □ (Parser P C) ]
  lift2 = Box.map2

  lift2l : ∀[ Parser P A ⇒ Parser P B ⇒ Parser P C ] ->
           ∀[ □ (Parser P A) ⇒ Parser P B ⇒ □ (Parser P C) ]
  lift2l f a b = lift2 f a (box b)

  lift2r : ∀[ Parser P A ⇒ Parser P B ⇒ Parser P C ] ->
           ∀[ Parser P A ⇒ □ (Parser P B) ⇒ □ (Parser P C) ]
  lift2r f a b = lift2 f (box a) b

 module _ {A B : Set≤ l} where

  infixr 5 _<$>_
  _<$>_ : (theSet A → theSet B) → ∀[ Parser P A ⇒ Parser P B ]
  runParser (f <$> p) lt s = S.map f 𝕄.<$> (runParser p lt s)

  infixr 5 _<$_
  _<$_ : theSet B → ∀[ Parser P A ⇒ Parser P B ]
  b <$ p = const b <$> p

  _&?>>=_ : ∀[ Parser P A ⇒ (const (theSet A) ⇒ □ Parser P B) ⇒
               Parser P (A × Maybe B) ]
  runParser (A &?>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (Box.call (B (lower a)) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (S.and rA (S.map just rB)))
    𝕄.∣ 𝕄.return (lift (lower a , nothing) ^ p<m , s′)

  _&>>=_ : ∀[ Parser P A ⇒ (const (theSet A) ⇒ □ Parser P B) ⇒ Parser P (A × B) ]
  runParser (A &>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (Box.call (B (lower a)) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (S.and rA rB))

 module _ {A B : Set≤ l} where

  _?&>>=_ : ∀[ Parser P A ⇒ (const (theSet (Maybe A)) ⇒ Parser P B) ⇒
            Parser P (Maybe A × B) ]
  A ?&>>= B = (Product.map₁ just <$> A &>>= λ a → box (B (just a)))
          <|> ((nothing ,_)   <$> B nothing)

 module _ {A B : Set≤ l} where

  _>>=_ : ∀[ Parser P A ⇒ (const (theSet A) ⇒ □ Parser P B) ⇒ Parser P B ]
  A >>= B = proj₂ <$> A &>>= B

  infixl 4 _<&>_ _<&_ _&>_
  _<&>_ : ∀[ Parser P A ⇒ □ Parser P B ⇒ Parser P (A × B) ]
  A <&> B = A &>>= const B

  _<&_ : ∀[ Parser P A ⇒ □ Parser P B ⇒ Parser P A ]
  A <& B = proj₁ <$> (A <&> B)

  _&>_ : ∀[ Parser P A ⇒ □ Parser P B ⇒ Parser P B ]
  A &> B = proj₂ <$> (A <&> B)

 module _ {A : Set≤ l} where

  alts : ∀[ List.List ∘′ Parser P A ⇒ Parser P A ]
  alts = List.foldr _<|>_ fail

  ands : ∀[ List⁺.List⁺ ∘′ Parser P A ⇒ Parser P (List⁺ A) ]
  ands ps = List⁺.foldr₁ (λ p ps → uncurry List⁺._⁺++⁺_ <$> (p <&> box ps))
            (List⁺.map (List⁺.[_] <$>_) ps)

 module _ {A B : Set≤ l} where

  infixl 4 _<*>_
  _<*>_ : ∀[ Parser P (A ⟶ B) ⇒ □ Parser P A ⇒ Parser P B ]
  F <*> A = uncurry _$_ <$> (F <&> A)

  infixl 4 _<&M>_ _<&M_ _&M>_
  _<&M>_ : ∀[ Parser P A ⇒ const (P.M (Lift B)) ⇒ Parser P (A × B) ]
  runParser (A <&M> B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA → B 𝕄.>>= λ b →
    𝕄.return (S.map (_, lower b) rA)

  _<&M_ : ∀[ Parser P A ⇒ const (P.M (Lift B)) ⇒ Parser P A ]
  A <&M B = proj₁ <$> (A <&M> B)

  _&M>_ : ∀[ Parser P A ⇒ const (P.M (Lift B)) ⇒ Parser P B ]
  A &M> B = proj₂ <$> (A <&M> B)

  infixl 4 _<&?>_ _<&?_ _&?>_
  _<&?>_ : ∀[ Parser P A ⇒ □ Parser P B ⇒ Parser P (A × Maybe B) ]
  A <&?> B = A &?>>= const B

  _<&?_ : ∀[ Parser P A ⇒ □ Parser P B ⇒ Parser P A ]
  A <&? B = proj₁ <$> (A <&?> B)

  _&?>_ : ∀[ Parser P A ⇒ □ Parser P B ⇒ Parser P (Maybe B) ]
  A &?> B = proj₂ <$> (A <&?> B)

  infixr 3 _<⊎>_
  _<⊎>_ : ∀[ Parser P A ⇒ Parser P B ⇒ Parser P (A ⊎ B) ]
  A <⊎> B = inj₁ <$> A <|> inj₂ <$> B

  infixl 4 _<?&>_ _<?&_ _?&>_
  _<?&>_ : ∀[ Parser P A ⇒ Parser P B ⇒ Parser P (Maybe A × B) ]
  A <?&> B = just <$> A <&> box B <|> (nothing ,_) <$> B

  _<?&_ : ∀[ Parser P A ⇒ Parser P B ⇒ Parser P (Maybe A) ]
  A <?& B = proj₁ <$> (A <?&> B)

  _?&>_ : ∀[ Parser P A ⇒ Parser P B ⇒ Parser P B ]
  A ?&> B = proj₂ <$> (A <?&> B)

  infixl 4 _<M&>_ _<M&_ _M&>_
  _<M&>_ : ∀[ const (P.M (Lift A)) ⇒ Parser P B ⇒ Parser P (A × B) ]
  runParser (A <M&> B) m≤n s =
    A 𝕄.>>= λ a → S.map (lower a ,_) 𝕄.<$> runParser B m≤n s

  _<M&_ : ∀[ const (P.M (Lift A)) ⇒ Parser P B ⇒ Parser P A ]
  A <M& B = proj₁ <$> (A <M&> B)

  _M&>_ : ∀[ const (P.M (Lift A)) ⇒ Parser P B ⇒ Parser P B ]
  A M&> B = proj₂ <$> (A <M&> B)

 module _ {A B C : Set≤ l} where

  between : ∀[ Parser P A ⇒ □ Parser P C ⇒ □ Parser P B ⇒ Parser P B ]
  between A C B = A &> B <& C

  between? : ∀[ Parser P A ⇒ □ Parser P C ⇒ Parser P B ⇒ Parser P B ]
  between? A C B = between A C (box B) <|> B

 module _ {{eq? : DecidableEquality (theSet Tok)}} where

  anyOf : theSet (List Tok) → ∀[ Parser P P.Tok ]
  anyOf ts = guard (λ c → not (null ts) ∧ List.any (⌊_⌋ ∘ decide eq? c) ts) anyTok

  exact : theSet Tok → ∀[ Parser P P.Tok ]
  exact = anyOf ∘′ List.[_]

  exacts : theSet (List⁺ Tok) → ∀[ Parser P (List⁺ P.Tok) ]
  exacts ts = ands (List⁺.map (λ t → exact t) ts)

  noneOf : theSet (List Tok) → ∀[ Parser P P.Tok ]
  noneOf ts = maybeTok $ λ t → case Any.any? (eq? .decide t) ts of λ where
    (yes p) → nothing
    (no ¬p) → just t

  anyTokenBut : theSet Tok → ∀[ Parser P P.Tok ]
  anyTokenBut = noneOf ∘′ List.[_]

 module _ {A : Set≤ l} where

  schainl : ∀[ Success Toks A ⇒ □ Parser P (A ⟶ A) ⇒ P.M ∘ Success P.Toks A ]
  schainl = Box.fix goal $ λ rec sA op → rest rec sA op 𝕄.∣ 𝕄.return sA where

    goal = Success P.Toks A ⇒ □ Parser P (A ⟶ A) ⇒ P.M ∘ Success P.Toks A

    rest : ∀[ □ goal ⇒ goal ]
    rest rec (a ^ p<m , s) op = runParser (Box.call op p<m) ≤-refl s 𝕄.>>= λ sOp →
          Box.call rec p<m (S.map (_$ lower a) sOp) (Box.<-lower p<m op) 𝕄.>>=
          𝕄.return ∘ <-lift p<m

  iterate : ∀[ Parser P A ⇒ □ Parser P (A ⟶ A) ⇒ Parser P A ]
  runParser (iterate {n} a op) m≤n s =
    runParser a m≤n s 𝕄.>>= λ sA → schainl sA $ Box.≤-lower m≤n op

 module _ {A B : Set≤ l} where

  hchainl : ∀[ Parser P A ⇒ □ Parser P (A ⟶ B ⟶ A) ⇒ □ Parser P B ⇒
              Parser P A ]
  hchainl A op B = iterate A (Box.map2 _<*>_ (Box.map (flip <$>_) op) (Box.duplicate B))

 module _ {A : Set≤ l} where

  chainl1 : ∀[ Parser P A ⇒ □ Parser P (A ⟶ A ⟶ A) ⇒ Parser P A ]
  chainl1 a op = hchainl a op (box a)

  chainr1 : ∀[ Parser P A ⇒ □ Parser P (A ⟶ A ⟶ A) ⇒ Parser P A ]
  chainr1 = Box.fix goal $ λ rec A op → mkParser λ m≤n s →
            runParser A m≤n s 𝕄.>>= λ sA →
            rest (Box.≤-lower m≤n rec) (≤-lower m≤n A) (Box.≤-lower m≤n op) sA
            𝕄.∣  𝕄.return sA where

    goal = Parser P A ⇒ □ Parser P (A ⟶ A ⟶ A) ⇒ Parser P A

    rest : ∀[ □ goal ⇒ Parser P A ⇒ □ Parser P (A ⟶ A ⟶ A) ⇒
             Success P.Toks A ⇒ P.M ∘ Success P.Toks A ]
    rest rec A op sA@(a ^ m<n , s) = runParser (Box.call op m<n) ≤-refl s 𝕄.>>=
          λ sOp → let (f ^ p<m , s′) = sOp ; .p<n : _ < _; p<n = <-trans p<m m<n in
          let rec′ = Box.call rec p<n (<-lower p<n A) (Box.<-lower p<n op) in
          <-lift p<n ∘ S.map (lower f (lower a) $_) 𝕄.<$> runParser rec′ ≤-refl s′

  head+tail : ∀[ Parser P A ⇒ □ Parser P A ⇒ Parser P (List⁺ A) ]
  head+tail hd tl = List⁺.reverse
                <$> (iterate {List⁺ A} (List⁺.[_] <$> hd) (Box.map (List⁺._∷⁺_ <$>_) tl))

  list⁺ : ∀[ Parser P A ⇒ Parser P (List⁺ A) ]
  list⁺ = Box.fix (Parser P A ⇒ Parser P (List⁺ A)) $ λ rec pA →
          uncurry (λ hd → (hd ∷_) ∘ maybe List⁺.toList [])
          <$> (pA <&?> (Box.app rec (box pA)))
