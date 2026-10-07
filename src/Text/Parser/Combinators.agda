{-# OPTIONS --without-K --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Text.Parser.Combinators {l} {P : Parameters l} where

open import Level.Bounded as Level≤ hiding (map)

open import Relation.Unary using (IUniversal; _⇒_)
open import Induction.Nat.Strong as Box using (□_)
open import Data.Nat.Base using (ℕ; _≤_; _<_)

open import Data.Bool.Base as Bool using (Bool; if_then_else_; not; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.List.Base as List using (_∷_; []; null)
open import Data.List.NonEmpty as List⁺ using (_∷⁺_ ; _∷_)
open import Data.Maybe.Base as M using (just; nothing; maybe)
open import Data.Nat.Base using (suc; NonZero)
open import Data.Product as Product using (Σ-syntax; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Data.Vec.Base as Vec using (_∷_; [])

open import Data.Nat.Properties as Nat using (≤-refl; ≤-trans; <⇒≤; <-trans)
import Data.List.Relation.Unary.Any as Any
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality.Decidable.Core using (DecidableEquality; decide)

open import Effect.Monad using (RawMonadPlus)
open import Data.List.Sized.Interface using (Sized)

open import Function.Base using (const; _$_; _∘_; _∘′_; flip; case_of_)

open import Text.Parser.Types.Core
open import Text.Parser.Types P
open import Text.Parser.Success P as S hiding (guardM)

open Parameters P

module _ {{𝕊 : Sized Tok Toks}} {{𝕄 : RawMonadPlus M}}
         where

 private module 𝕄 = RawMonadPlus 𝕄

 anyTok : ∀[ Parser Tok ]
 runParser anyTok m≤n s = case view (lower s) of λ where
   nothing  → 𝕄.∅
   (just t) → t 𝕄.<$ recordToken (lower $ Success.value t)

 module _ {A B : Set≤ l} where

  guardM : theSet (A ⟶ Maybe B) → ∀[ Parser A ⇒ Parser B ]
  runParser (guardM p A) m≤n s =
    runParser A m≤n s 𝕄.>>= maybe 𝕄.pure 𝕄.∅ ∘′ S.guardM p

 module _ {A : Set≤ l} where

  guard : theSet (A ⟶ [ Bool ]) → ∀[ Parser A ⇒ Parser A ]
  guard p = guardM (λ a → if p a then just a else nothing)

  maybeTok : theSet (Tok ⟶ Maybe A) → ∀[ Parser A ]
  maybeTok p = guardM p anyTok

  ≤-lower : {m n : ℕ} → .(m ≤ n) → Parser A n → Parser A m
  runParser (≤-lower m≤n A) p≤m = runParser A (≤-trans p≤m m≤n)

  <-lower : {m n : ℕ} → .(m < n) → Parser A n → Parser A m
  <-lower m<n = ≤-lower (<⇒≤ m<n)

  box : ∀[ Parser A ⇒ □ Parser A ]
  box = Box.≤-close ≤-lower

  fail : ∀[ Parser A ]
  runParser fail _ _ = 𝕄.∅

  infixr 3 _<|>_
  _<|>_ : ∀[ Parser A ⇒ Parser A ⇒ Parser A ]
  runParser (A₁ <|> A₂) m≤n s = runParser A₁ m≤n s 𝕄.∣ runParser A₂ m≤n s

 module _ {A B C : Set≤ l} where

  lift2 : ∀[ Parser A ⇒ Parser B ⇒ Parser C ] →
          ∀[ □ (Parser A) ⇒ □ (Parser B) ⇒ □ (Parser C) ]
  lift2 = Box.map2

  lift2l : ∀[ Parser A ⇒ Parser B ⇒ Parser C ] ->
           ∀[ □ (Parser A) ⇒ Parser B ⇒ □ (Parser C) ]
  lift2l f a b = lift2 f a (box b)

  lift2r : ∀[ Parser A ⇒ Parser B ⇒ Parser C ] ->
           ∀[ Parser A ⇒ □ (Parser B) ⇒ □ (Parser C) ]
  lift2r f a b = lift2 f (box a) b

 module _ {A : Set≤ l} {b} {{b≤l : b ≤l l}} {B : theSet A → Set b} where

  _&?>>=_ : ∀ {n} → Parser A n → ((a : theSet A) → (□ Parser (mkSet≤ (B a))) n) →
            Parser (Σ A λ a → M.Maybe (B a)) n
  runParser (A &?>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (Box.call (B (lower a)) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
    𝕄.pure (S.and rA (S.map just rB)))
    𝕄.∣ 𝕄.pure ((lift (lower a , nothing)) ^ p<m , s′)

  _&>>=_ : ∀ {n} → Parser A n → ((a : theSet A) → (□ Parser (mkSet≤ (B a))) n) →
           Parser (Σ A B) n
  runParser (A &>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (Box.call (B (lower a)) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.pure (S.and rA rB))

 module _ {A B : Set≤ l} where

  infixr 5 _<$>_
  _<$>_ : theSet (A ⟶ B) → ∀[ Parser A ⇒ Parser B ]
  runParser (f <$> p) lt s = S.map f 𝕄.<$> runParser p lt s

  infixr 5 _<$_
  _<$_ : theSet B → ∀[ Parser A ⇒ Parser B ]
  b <$ p = const b <$> p

 module _ {A : Set≤ l} {b} {{b≤l : b ≤l l}} {B : theSet (Maybe A) → Set b} where

  _?&>>=_ : ∀ {n} → Parser A n → ((ma : theSet (Maybe A)) → Parser (mkSet≤ (B ma)) n) →
            Parser (Σ (Maybe A) B) n
  runParser (_?&>>=_ {n} pA pB) m≤n s =
   let p : Parser (A ⊎ mkSet≤ (B nothing)) n
       p = inj₁ <$> pA <|> inj₂ <$> pB nothing
   in runParser p m≤n s 𝕄.>>= λ (v ^ p<m , ts) → case lower v of λ where
        (inj₂ b) → 𝕄.pure (lift (nothing , b) ^ p<m , ts)
        (inj₁ a) → (S.map (just a ,_) ∘′ <-lift p<m)
             𝕄.<$> runParser (pB (just a)) (≤-trans (<⇒≤ p<m) m≤n) ts

 module _ {A B : Set≤ l} where

  _&?>>=′_ : ∀[ Parser A ⇒ (const (theSet A) ⇒ □ Parser B) ⇒
                Parser (A × Maybe B) ]
  runParser (A &?>>=′ B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (Box.call (B (lower a)) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.pure (S.and′ rA (S.map just rB)))
    𝕄.∣ 𝕄.pure (lift (lower a , nothing) ^ p<m , s′)

  _&>>=′_ : ∀[ Parser A ⇒ (const (theSet A) ⇒ □ Parser B) ⇒ Parser (A × B) ]
  runParser (A &>>=′ B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (Box.call (B (lower a)) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.pure (S.and′ rA rB))

 module _ {A B : Set≤ l} where

  _?&>>=′_ : ∀[ Parser A ⇒ (const (theSet (Maybe A)) ⇒ Parser B) ⇒
                Parser (Maybe A × B) ]
  _?&>>=′_ = _?&>>=_

 module _ {A B : Set≤ l} where

  _>>=_ : ∀[ Parser A ⇒ (const (theSet A) ⇒ □ Parser B) ⇒ Parser B ]
  A >>= B = proj₂ <$> A &>>=′ B

  infixl 4 _<&>_ _<&_ _&>_
  _<&>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A × B) ]
  A <&> B = A &>>=′ const B

  _<&_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
  A <& B = proj₁ <$> (A <&> B)

  _&>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser B ]
  A &> B = proj₂ <$> (A <&> B)

 module _ {A : Set≤ l} where

  alts : ∀[ List.List ∘′ Parser A ⇒ Parser A ]
  alts = List.foldr _<|>_ fail

  ands : ∀[ List⁺.List⁺ ∘′ Parser A ⇒ Parser (List⁺ A) ]
  ands ps = List⁺.foldr₁ (λ p ps → uncurry List⁺._⁺++⁺_ <$> (p <&> box ps))
            (List⁺.map (List⁺.[_] <$>_) ps)

 module _ {A B : Set≤ l} where

  infixl 4 _<*>_
  _<*>_ : ∀[ Parser (A ⟶ B) ⇒ □ Parser A ⇒ Parser B ]
  F <*> A = uncurry _$_ <$> (F <&> A)

  infixl 4 _<&M>_ _<&M_ _&M>_
  _<&M>_ : ∀[ Parser A ⇒ const (M (Lift B)) ⇒ Parser (A × B) ]
  runParser (A <&M> B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA → B 𝕄.>>= λ b →
    𝕄.pure (S.map (_, lower b) rA)

  _<&M_ : ∀[ Parser A ⇒ const (M (Lift B)) ⇒ Parser A ]
  A <&M B = proj₁ <$> (A <&M> B)

  _&M>_ : ∀[ Parser A ⇒ const (M (Lift B)) ⇒ Parser B ]
  A &M> B = proj₂ <$> (A <&M> B)

  infixl 4 _<&?>_ _<&?_ _&?>_
  _<&?>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A × Maybe B) ]
  A <&?> B = A &?>>=′ const B

  _<&?_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
  A <&? B = proj₁ <$> (A <&?> B)

  _&?>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (Maybe B) ]
  A &?> B = proj₂ <$> (A <&?> B)

  infixr 3 _<⊎>_
  _<⊎>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (A ⊎ B) ]
  A <⊎> B = inj₁ <$> A <|> inj₂ <$> B

 module _ {A B R : Set≤ l} where

  <[_,_]> : ∀[ const (theSet A → theSet R) ⇒ (const (theSet B) ⇒ □ Parser R) ⇒
               Parser (A ⊎ B) ⇒ Parser R ]
  runParser (<[ f , k ]> A⊎B) m≤n s =
    runParser A⊎B m≤n s 𝕄.>>= λ rA⊎B → let (v ^ p<m , s′) = rA⊎B in
    case lower v of λ where
      (inj₁ a) → 𝕄.pure (lift (f a) ^ p<m , s′)
      (inj₂ b) → <-lift p<m 𝕄.<$> runParser (Box.call (k b) (≤-trans p<m m≤n)) ≤-refl s′

 module _ {A B : Set≤ l} where

  infixl 4 _<?&>_ _<?&_ _?&>_
  _<?&>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybe A × B) ]
  A <?&> B = just <$> A <&> box B <|> (nothing ,_) <$> B

  _<?&_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybe A) ]
  A <?& B = proj₁ <$> (A <?&> B)

  _?&>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser B ]
  A ?&> B = proj₂ <$> (A <?&> B)

  infixl 4 _<M&>_ _<M&_ _M&>_
  _<M&>_ : ∀[ const (M (Lift A)) ⇒ Parser B ⇒ Parser (A × B) ]
  runParser (A <M&> B) m≤n s =
    A 𝕄.>>= λ a → S.map (lower a ,_) 𝕄.<$> runParser B m≤n s

  _<M&_ : ∀[ const (M (Lift A)) ⇒ Parser B ⇒ Parser A ]
  A <M& B = proj₁ <$> (A <M&> B)

  _M&>_ : ∀[ const (M (Lift A)) ⇒ Parser B ⇒ Parser B ]
  A M&> B = proj₂ <$> (A <M&> B)

 module _ {A B C : Set≤ l} where

  between : ∀[ Parser A ⇒ □ Parser C ⇒ □ Parser B ⇒ Parser B ]
  between A C B = A &> B <& C

  between? : ∀[ Parser A ⇒ □ Parser C ⇒ Parser B ⇒ Parser B ]
  between? A C B = between A C (box B) <|> B

 module _ {{eq? : DecidableEquality (theSet Tok)}} where

  anyOf : theSet (List Tok) → ∀[ Parser Tok ]
  anyOf ts = guard (λ c → not (null ts) ∧ any (⌊_⌋ ∘ decide eq? c) ts) anyTok

  exact : theSet Tok → ∀[ Parser Tok ]
  exact = anyOf ∘′ List.[_]

  exacts : theSet (List⁺ Tok) → ∀[ Parser (List⁺ Tok) ]
  exacts ts = ands (List⁺.map (λ t → exact t) ts)

  noneOf : theSet (List Tok) → ∀[ Parser Tok ]
  noneOf ts = maybeTok $ λ t → case Any.any? (eq? .decide t) ts of λ where
    (yes p) → nothing
    (no ¬p) → just t

  anyTokenBut : theSet Tok → ∀[ Parser Tok ]
  anyTokenBut = noneOf ∘′ List.[_]

 module _ {A : Set≤ l} where

  schainl : ∀[ Success Toks A ⇒ □ Parser (A ⟶ A) ⇒ M ∘′ Success Toks A ]
  schainl = Box.fix goal $ λ rec sA op → rest rec sA op 𝕄.∣ 𝕄.pure sA where

    goal = Success Toks A ⇒ □ Parser (A ⟶ A) ⇒ M ∘′ Success Toks A

    rest : ∀[ □ goal ⇒ goal ]
    rest rec (a ^ p<m , s) op = runParser (Box.call op p<m) ≤-refl s 𝕄.>>= λ sOp →
          Box.call rec p<m (S.map (_$ lower a) sOp) (Box.<-lower p<m op) 𝕄.>>=
          𝕄.pure ∘′ <-lift p<m

  iterate : ∀[ Parser A ⇒ □ Parser (A ⟶ A) ⇒ Parser A ]
  runParser (iterate {n} a op) m≤n s =
    runParser a m≤n s 𝕄.>>= λ sA → schainl sA $ Box.≤-lower m≤n op

 module _ {A B : Set≤ l} where

  hchainl : ∀[ Parser A ⇒ □ Parser (A ⟶ B ⟶ A) ⇒ □ Parser B ⇒
              Parser A ]
  hchainl A op B = iterate A (Box.map2 _<*>_ (Box.map (flip <$>_) op) (Box.duplicate B))

 module _ {A : Set≤ l} where

  chainl1 : ∀[ Parser A ⇒ □ Parser (A ⟶ A ⟶ A) ⇒ Parser A ]
  chainl1 a op = hchainl a op (box a)

  chainr1 : ∀[ Parser A ⇒ □ Parser (A ⟶ A ⟶ A) ⇒ Parser A ]
  chainr1 = Box.fix goal $ λ rec A op → mkParser λ m≤n s →
            runParser A m≤n s 𝕄.>>= λ sA →
            rest (Box.≤-lower m≤n rec) (≤-lower m≤n A) (Box.≤-lower m≤n op) sA
            𝕄.∣  𝕄.pure sA where

    goal = Parser A ⇒ □ Parser (A ⟶ A ⟶ A) ⇒ Parser A

    rest : ∀[ □ goal ⇒ Parser A ⇒ □ Parser (A ⟶ A ⟶ A) ⇒
             Success Toks A ⇒ M ∘′ Success Toks A ]
    rest rec A op sA@(a ^ m<n , s) = runParser (Box.call op m<n) ≤-refl s 𝕄.>>=
          λ sOp → let (f ^ p<m , s′) = sOp ; .p<n : _ < _; p<n = <-trans p<m m<n in
          let rec′ = Box.call rec p<n (<-lower p<n A) (Box.<-lower p<n op) in
          <-lift p<n ∘′ S.map (lower f (lower a) $_) 𝕄.<$> runParser rec′ ≤-refl s′

  head+tail : ∀[ Parser A ⇒ □ Parser A ⇒ Parser (List⁺ A) ]
  head+tail hd tl = List⁺.reverse
                <$> (iterate {List⁺ A} (List⁺.[_] <$> hd) (Box.map (List⁺._∷⁺_ <$>_) tl))

  list⁺ : ∀[ Parser A ⇒ Parser (List⁺ A) ]
  list⁺ = Box.fix (Parser A ⇒ Parser (List⁺ A)) $ λ rec pA →
          uncurry (λ hd → (hd ∷_) ∘′ maybe List⁺.toList [])
          <$> (pA <&?> (Box.app rec (box pA)))

  replicate : (n : ℕ) → {{NonZero n}} → ∀[ Parser A ⇒ Parser (Vec A n) ]
  replicate 1               p = Vec.[_] <$> p
  replicate (suc n@(suc _)) p = uncurry Vec._∷_ <$> (p <&> box (replicate n p))
