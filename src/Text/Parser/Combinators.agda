module Text.Parser.Combinators where

open import Relation.Unary.Indexed
open import Induction.Nat.Strong as Box hiding (≤-lower ; <-lower)
open import Data.Nat.Base hiding (_^_)
open import Data.Nat.LTE

open import Data.Sum as S
open import Data.Product as P hiding (,_)
open import Data.Maybe.Base
open import Data.Char
open import Data.Bool.Base
open import Data.Nat.Properties using (<-trans)
open import Data.List.Base as List hiding ([_] ; any)
open import Data.List.NonEmpty as NonEmpty using (List⁺ ; _∷⁺_ ; _∷_)
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Agda.Builtin.Equality
import Data.String as String
open String using () renaming (String to Text)

open import Category.Monad
open import Data.List.Sized.Interface
open import Text.Parser.Success as Success hiding (guardM)
open import Function

record Parser (Tok : Set) (Toks : ℕ → Set) (M : Set → Set) (A : Set) (n : ℕ) : Set where
  constructor mkParser
  field runParser :  ∀ {m} → .(m ≤ n) → Toks m →
                     M (Success Tok Toks A m)
open Parser public

module _ {Tok : Set} {Toks : ℕ → Set} {{𝕊 : Sized Tok Toks}}
         {M : Set → Set} {{𝕄 : RawMonadPlus M}} where

 private module 𝕄 = RawMonadPlus 𝕄

 anyTok : [ Parser Tok Toks M Tok ]
 runParser anyTok m≤n s = maybe′ 𝕄.return 𝕄.∅ (view s)

 module _ {A B : Set} where

  guardM : (A → Maybe B) → [ Parser Tok Toks M A ⟶ Parser Tok Toks M B ]
  runParser (guardM p A) m≤n s =
    runParser A m≤n s 𝕄.>>= maybe 𝕄.return 𝕄.∅ ∘ Success.guardM p

 module _ {A : Set} where

  guard : (A → Bool) → [ Parser Tok Toks M A ⟶ Parser Tok Toks M A ]
  guard p = guardM (λ a → if p a then just a else nothing)

  maybeTok : (Tok → Maybe A) → [ Parser Tok Toks M A ]
  maybeTok p = guardM p anyTok

  ≤-lower : {m n : ℕ} → .(m ≤ n) → Parser Tok Toks M A n → Parser Tok Toks M A m
  runParser (≤-lower m≤n A) p≤m = runParser A (≤-trans p≤m m≤n)

  <-lower : {m n : ℕ} → .(m < n) → Parser Tok Toks M A n → Parser Tok Toks M A m
  <-lower m<n = ≤-lower (<⇒≤ m<n)

  box : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M A ]
  box = ≤-close ≤-lower

  fail : [ Parser Tok Toks M A ]
  runParser fail _ _ = 𝕄.∅

  infixr 3 _<|>_
  _<|>_ : [ Parser Tok Toks M A ⟶ Parser Tok Toks M A ⟶ Parser Tok Toks M A ]
  runParser (A₁ <|> A₂) m≤n s = runParser A₁ m≤n s 𝕄.∣ runParser A₂ m≤n s

 module _ {A B : Set} where

  infixr 5 _<$>_
  _<$>_ : (A → B) → [ Parser Tok Toks M A ⟶ Parser Tok Toks M B ]
  runParser (f <$> p) lt s = Success.map f 𝕄.<$> (runParser p lt s)

  infixr 5 _<$_
  _<$_ : B → [ Parser Tok Toks M A ⟶ Parser Tok Toks M B ]
  b <$ p = const b <$> p

  _&?>>=_ : [ Parser Tok Toks M A ⟶ (const A ⟶ □ Parser Tok Toks M B) ⟶
              Parser Tok Toks M (A × Maybe B) ]
  runParser (A &?>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (Success.and rA (Success.map just rB)))
    𝕄.∣ 𝕄.return (a , nothing ^ p<m , s′)

  _&>>=_ : [ Parser Tok Toks M A ⟶ (const A ⟶ □ Parser Tok Toks M B) ⟶ Parser Tok Toks M (A × B) ]
  runParser (A &>>= B) m≤n s =
    runParser A m≤n s 𝕄.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ 𝕄.>>= λ rB →
     𝕄.return (Success.and rA rB))

 module _ {A B : Set} where

  _>>=_ : [ Parser Tok Toks M A ⟶ (const A ⟶ □ Parser Tok Toks M B) ⟶ Parser Tok Toks M B ]
  A >>= B = proj₂ <$> A &>>= B

  infixl 4 _<&>_ _<&_ _&>_
  _<&>_ : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M B ⟶ Parser Tok Toks M (A × B) ]
  A <&> B = A &>>= const B

  _<&_ : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M B ⟶ Parser Tok Toks M A ]
  A <& B = proj₁ <$> (A <&> B)

  _&>_ : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M B ⟶ Parser Tok Toks M B ]
  A &> B = proj₂ <$> (A <&> B)

 module _ {A : Set} where

  alts : [ List ⊚ Parser Tok Toks M A ⟶ Parser Tok Toks M A ]
  alts = List.foldr _<|>_ fail

  ands : [ List⁺ ⊚ Parser Tok Toks M A ⟶ Parser Tok Toks M (List⁺ A) ]
  ands ps = NonEmpty.foldr₁ (λ p ps → uncurry NonEmpty._⁺++⁺_ <$> (p <&> box ps))
            (NonEmpty.map (NonEmpty.[_] <$>_) ps)

 module _ {A B : Set} where

  infixl 4 _<*>_
  _<*>_ : [ Parser Tok Toks M (A → B) ⟶ □ Parser Tok Toks M A ⟶ Parser Tok Toks M B ]
  F <*> A = uncurry _$_ <$> (F <&> A)

  infixl 4 _<&?>_ _<&?_ _&?>_
  _<&?>_ : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M B ⟶ Parser Tok Toks M (A × Maybe B) ]
  A <&?> B = A &?>>= const B

  _<&?_ : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M B ⟶ Parser Tok Toks M A ]
  A <&? B = proj₁ <$> (A <&?> B)

  _&?>_ : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M B ⟶ Parser Tok Toks M (Maybe B) ]
  A &?> B = proj₂ <$> (A <&?> B)

  infixr 3 _<⊎>_
  _<⊎>_ : [ Parser Tok Toks M A ⟶ Parser Tok Toks M B ⟶ Parser Tok Toks M (A ⊎ B) ]
  A <⊎> B = inj₁ <$> A <|> inj₂ <$> B

  infixl 4 _<?&>_ _<?&_ _?&>_
  _<?&>_ : [ Parser Tok Toks M A ⟶ Parser Tok Toks M B ⟶ Parser Tok Toks M (Maybe A × B) ]
  A <?&> B = just <$> A <&> box B <|> (nothing ,_) <$> B

  _<?&_ : [ Parser Tok Toks M A ⟶ Parser Tok Toks M B ⟶ Parser Tok Toks M (Maybe A) ]
  A <?& B = proj₁ <$> (A <?&> B)

  _?&>_ : [ Parser Tok Toks M A ⟶ Parser Tok Toks M B ⟶ Parser Tok Toks M B ]
  A ?&> B = proj₂ <$> (A <?&> B)

 module _ {A B C : Set} where

  between : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M C ⟶ □ Parser Tok Toks M B ⟶ Parser Tok Toks M B ]
  between A C B = A &> B <& C

  between? : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M C ⟶ Parser Tok Toks M B ⟶ Parser Tok Toks M B ]
  between? A C B = between A C (box B) <|> B

 module _ {{eq? : Decidable {A = Tok} _≡_}} where

  anyOf : List Tok → [ Parser Tok Toks M Tok ]
  anyOf ts = guard (λ c → not (null ts) ∧ List.any (⌊_⌋ ∘ eq? c) ts) anyTok

  exact : Tok → [ Parser Tok Toks M Tok ]
  exact = anyOf ∘ List.[_]

  exacts : List⁺ Tok → [ Parser Tok Toks M (List⁺ Tok) ]
  exacts ts = ands (NonEmpty.map (λ t → exact t) ts)

 module _ {A : Set} where

  schainl : [ Success Tok Toks A ⟶ □ Parser Tok Toks M (A → A) ⟶ M ∘ Success Tok Toks A ]
  schainl = fix goal $ λ rec sA op → rest rec sA op 𝕄.∣ 𝕄.return sA where

    goal = Success Tok Toks A ⟶ □ Parser Tok Toks M (A → A) ⟶ M ∘ Success Tok Toks A

    rest : [ □ goal ⟶ goal ]
    rest rec (a ^ p<m , s) op = runParser (call op p<m) ≤-refl s 𝕄.>>= λ sOp →
          call rec p<m (Success.map (_$ a) sOp) (Box.<-lower p<m op) 𝕄.>>=
          𝕄.return ∘ <-lift p<m

  iterate : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M (A → A) ⟶ Parser Tok Toks M A ]
  runParser (iterate {n} a op) m≤n s =
    runParser a m≤n s 𝕄.>>= λ sA → schainl sA $ Box.≤-lower m≤n op

 module _ {A B : Set} where

  hchainl : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M (A → B → A) ⟶ □ Parser Tok Toks M B ⟶
              Parser Tok Toks M A ]
  hchainl A op B = iterate A (map2 _<*>_ (Box.map (flip <$>_) op) (duplicate B))

 module _ {A : Set} where

  chainl1 : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M (A → A → A) ⟶ Parser Tok Toks M A ]
  chainl1 a op = hchainl a op (box a)

  chainr1 : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M (A → A → A) ⟶ Parser Tok Toks M A ]
  chainr1 = fix goal $ λ rec A op → mkParser λ m≤n s →
            runParser A m≤n s 𝕄.>>= λ sA →
            rest (Box.≤-lower m≤n rec) (≤-lower m≤n A) (Box.≤-lower m≤n op) sA
            𝕄.∣  𝕄.return sA where

    goal = Parser Tok Toks M A ⟶ □ Parser Tok Toks M (A → A → A) ⟶ Parser Tok Toks M A

    rest : [ □ goal ⟶ Parser Tok Toks M A ⟶ □ Parser Tok Toks M (A → A → A) ⟶
             Success Tok Toks A ⟶ M ∘ Success Tok Toks A ]
    rest rec A op sA@(a ^ m<n , s) = runParser (call op m<n) ≤-refl s 𝕄.>>=
          λ sOp → let (f ^ p<m , s′) = sOp ; .p<n : _ < _; p<n = <-trans p<m m<n in
          let rec′ = call rec p<n (<-lower p<n A) (Box.<-lower p<n op) in
          <-lift p<n ∘ Success.map (f a $_) 𝕄.<$> runParser rec′ ≤-refl s′

  head+tail : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M A ⟶ Parser Tok Toks M (List⁺ A) ]
  head+tail hd tl = NonEmpty.reverse
                <$> (iterate (NonEmpty.[_] <$> hd) (Box.map (NonEmpty._∷⁺_ <$>_) tl))

  list⁺ : [ Parser Tok Toks M A ⟶ Parser Tok Toks M (List⁺ A) ]
  list⁺ = fix (Parser Tok Toks M A ⟶ Parser Tok Toks M (List⁺ A)) $ λ rec pA →
          uncurry (λ hd → (hd ∷_) ∘ maybe NonEmpty.toList [])
          <$> (pA <&?> (app rec (box pA)))
