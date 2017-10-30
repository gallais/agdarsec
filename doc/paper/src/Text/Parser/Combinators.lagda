\begin{code}
module Text.Parser.Combinators where

import Level
open import Relation.Unary.Indexed
open import Induction.Nat.Strong as Iℕ hiding (lower)
open import Data.Nat.Base
open import Data.Nat.LTE

open import Data.Vec hiding ([_] ; _∷ʳ_ ; map ; _>>=_)
open import Data.Sum as S
open import Data.Product as P hiding (,_)
open import Data.Maybe.Base
open import Data.Char
open import Data.Bool.Base
open import Data.Nat.Properties
open import Data.List as DataList hiding ([_] ; any ; module List ; sequence)
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

 private module List = RawMonadPlus (DataList.monadPlus {Level.zero})

\end{code}
%<*anyChar>
\begin{code}
 anyChar : [ Parser Char ]
 runParser anyChar _ s with s
 ... | []      = []
 ... | c ∷ cs  = (c ^ ≤-refl , cs) ∷ []
\end{code}
%</anyChar>
\begin{code}

 module _ {A B : Set} where

\end{code}
%<*guardM>
\begin{code}
  guardM : (A → Maybe B) → [ Parser A ⟶ Parser B ]
  runParser (guardM p A) m≤n s =
    gfilter (sequence ∘ Success.map p) (runParser A m≤n s)
\end{code}
%</guardM>
\begin{code}

 module _ {A : Set} where

  guard : (A → Bool) → [ Parser A ⟶ Parser A ]
  guard p = guardM (λ a → if p a then just a else nothing)

  maybeChar : (Char → Maybe A) → [ Parser A ]
  maybeChar p = guardM p anyChar

\end{code}
%<*box>
\begin{code}
  box : [ Parser A ⟶ □ Parser A ]
\end{code}
%</box>
\begin{code}
  runParser (call (box A) m<n) p≤m = runParser A (≤-trans p≤m (<⇒≤ m<n))

  lower : {m n : ℕ} → .(m ≤ n) → Parser A n → Parser A m
  runParser (lower m≤n A) p≤m = runParser A (≤-trans p≤m m≤n)
\end{code}
%<*fail>
\begin{code}
  fail : [ Parser A ]
\end{code}
%</fail>
\begin{code}
  runParser fail _ _ = []

  infixr 3 _<|>_
\end{code}
%<*disjunction>
\begin{code}
  _<|>_ : [ Parser A ⟶ Parser A ⟶ Parser A ]
\end{code}
%</disjunction>
\begin{code}
  runParser (p <|> q) m≤n s =
    runParser p m≤n s List.∣ runParser q m≤n s


 module _ {A B : Set} where

  infixr 5 _<$>_
\end{code}
%<*fmap>
\begin{code}
  _<$>_ : (A → B) → [ Parser A ⟶ Parser B ]
\end{code}
%</fmap>
\begin{code}
  runParser (f <$> p) lt s = Success.map f List.<$> runParser p lt s

  infixr 5 _<$_
  _<$_ : B → [ Parser A ⟶ Parser B ]
  b <$ p = const b <$> p

\end{code}
%<*mbind>
\begin{code}
  _&?>>=_ : [  Parser A ⟶ (κ A ⟶ □ Parser B) ⟶ Parser (A × Maybe B) ]
\end{code}
%</mbind>
\begin{code}

  runParser (A &?>>= B) m≤n s =
    runParser A m≤n s List.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ List.>>= λ rB →
     List.return (lift (<⇒≤ p<m) (Success.map ((a ,_) ∘ just) rB)))
    List.∣ List.return (a , nothing ^ p<m , s′)

  _&>>=_ : [ Parser A ⟶ (const A ⟶ □ Parser B) ⟶ Parser (A × B) ]
  runParser (A &>>= B) m≤n s =
    runParser A m≤n s List.>>= λ rA →
    let (a ^ p<m , s′) = rA in
    (runParser (call (B a) (≤-trans p<m m≤n)) ≤-refl s′ List.>>= λ rB →
     List.return (lift (<⇒≤ p<m) (Success.map (a ,_) rB)))

 module _ {A B : Set} where

  _>>=_ : [ Parser A ⟶ (const A ⟶ □ Parser B) ⟶ Parser B ]
  A >>= B = proj₂ <$> A &>>= B

  infixl 4 _<&>_ _<&_ _&>_
\end{code}
%<*conjunction>
\begin{code}
  _<&>_ : [ Parser A ⟶ □ Parser B ⟶ Parser (A × B) ]
\end{code}
%</conjunction>
\begin{code}
  A <&> B = A &>>= const B

  _<&_ : [ Parser A ⟶ □ Parser B ⟶ Parser A ]
  A <& B = proj₁ <$> (A <&> B)

  _&>_ : [ Parser A ⟶ □ Parser B ⟶ Parser B ]
  A &> B = proj₂ <$> (A <&> B)

 module arf {A : Set} where
\end{code}
%<*badsome>
\begin{code}
  some : [ Parser A ] → [ Parser (List⁺ A) ]
  some p =  fix _ $ λ rec →  uncurry _∷⁺_ <$> (p <&> rec)
                             <|> (_∷ []) <$> p
\end{code}
%</badsome>
\begin{code}

 module _ {A B : Set} where

  infixl 4 _<*>_
\end{code}
%<*apply>
\begin{code}
  _<*>_ : [ Parser (A → B) ⟶ □ Parser A ⟶ Parser B ]
  F <*> A = uncurry _$_ <$> (F <&> A)
\end{code}
%</apply>
\begin{code}

  infixl 4 _<&?>_ _<&?_ _&?>_
\end{code}
%<*conjunction2>
\begin{code}
  _<&?>_ : [ Parser A ⟶ □ Parser B ⟶ Parser (A × Maybe B) ]
  A <&?> B = A &?>>= const B
\end{code}
%</conjunction2>
\begin{code}

  _<&?_ : [ Parser A ⟶ □ Parser B ⟶ Parser A ]
  A <&? B = proj₁ <$> (A <&?> B)

  _&?>_ : [ Parser A ⟶ □ Parser B ⟶ Parser (Maybe B) ]
  A &?> B = proj₂ <$> (A <&?> B)

  infixr 3 _<⊎>_
\end{code}
%<*disjunction2>
\begin{code}
  _<⊎>_ : [ Parser A ⟶ Parser B ⟶ Parser (A ⊎ B) ]
\end{code}
%</disjunction2>
\begin{code}
  A <⊎> B = inj₁ <$> A <|> inj₂ <$> B
  infixl 4 _<?&>_ _<?&_ _?&>_
  _<?&>_ : [ Parser A ⟶ Parser B ⟶ Parser (Maybe A × B) ]
  runParser (A <?&> B) m≤n s =
    (runParser (A <⊎> B) m≤n s) List.>>= λ rA⊎B → let (a⊎b ^ p<m , s′) = rA⊎B in
    case a⊎b of λ where
      (inj₂ b) → List.return (nothing , b ^ p<m , s′)
      (inj₁ a) → let r = runParser ((just a ,_) <$> B) (≤-trans (<⇒≤ p<m) m≤n) s′
                 in lift (<⇒≤ p<m) List.<$> r

  _<?&_ : [ Parser A ⟶ Parser B ⟶ Parser (Maybe A) ]
  A <?& B = proj₁ <$> (A <?&> B)

  _?&>_ : [ Parser A ⟶ Parser B ⟶ Parser B ]
  A ?&> B = proj₂ <$> (A <?&> B)

 module _ {A : Set} where
\end{code}
%<*goodsome>
\begin{code}
  some : [ Parser A ] → [ Parser (List⁺ A) ]
  some p =  fix _ $ λ rec → cons <$> (p <&?> rec)
\end{code}
%</goodsome>
\begin{code}
   where
    cons : (A × Maybe (List⁺ A)) → List⁺ A
    cons (a , mas) = maybe (a ∷⁺_) (a ∷ []) mas

 module _ {A B C : Set} where

  between : [ Parser A ⟶ □ Parser C ⟶ □ Parser B ⟶ Parser B ]
  between A C B = A &> B <& C

  between? : [ Parser A ⟶ □ Parser C ⟶ Parser B ⟶ Parser B ]
  between? A C B = between A C (box B) <|> B

 module _ {{eq? : Decidable {A = Char} _≡_}} where

  anyOf : List Char → [ Parser Char ]
  anyOf ts = guard (λ c → not (null ts) ∧ DataList.any (⌊_⌋ ∘ eq? c) ts) anyChar

  exact : Char → [ Parser Char ]
  exact = anyOf ∘ DataList.[_]

  exacts : List⁺ Char → [ Parser (List⁺ Char) ]
  exacts (x ∷ xs) = go x xs where

    go : Char → List Char → [ Parser (List⁺ Char) ]
    go x []       = NonEmpty.[_] <$> exact x
    go x (y ∷ xs) = uncurry _∷⁺_ <$> (exact x <&> box (go y xs))

 module _ {A : Set} where
\end{code}
%<*schainl>
\begin{code}
  schainl : [ Success A ⟶ □ Parser (A → A) ⟶ List ∘ Success A ]
  schainl = fix _ $ λ rec sA op → rest rec sA op ∷ʳ sA where

    rest :  [ □ (Success A ⟶ □ Parser (A → A) ⟶ List ∘ Success A)
            ⟶ Success A ⟶ □ Parser (A → A) ⟶ List ∘ Success A ]
\end{code}
%</schainl>
\begin{code}

    rest rec (a ^ p<m , s) op = runParser (call op p<m) ≤-refl s List.>>= λ sOp →
          call rec p<m (Success.map (_$ a) sOp) (Iℕ.lower (<⇒≤ p<m) op) List.>>=
          List.return ∘ lift (<⇒≤ p<m)
\end{code}
%<*iterate>
\begin{code}
  iterate : [ Parser A ⟶ □ Parser (A → A) ⟶ Parser A ]
\end{code}
%</iterate>
\begin{code}
  runParser (iterate {n} a op) m≤n s =
    runParser a m≤n s List.>>= λ sA → schainl sA $ Iℕ.lower m≤n op

 module _ {A B : Set} where


\end{code}
%<*hchainl>
\begin{code}
  hchainl : [ Parser A ⟶ □ Parser (A → B → A) ⟶ □ Parser B ⟶ Parser A ]
\end{code}
%</hchainl>
\begin{code}
  hchainl A op B = iterate A (map2 _<*>_ (Iℕ.map (flip <$>_) op) (duplicate B))

 module _ {A : Set} where

  chainl1 : [ Parser A ⟶ □ Parser (A → A → A) ⟶ Parser A ]
  chainl1 a op = hchainl a op (box a)

  chainr1 : [ Parser A ⟶ □ Parser (A → A → A) ⟶ Parser A ]
  chainr1 = fix goal $ λ rec A op → mkParser λ m≤n s →
            runParser A m≤n s List.>>= λ sA →
            rest (Iℕ.lower m≤n rec) (lower m≤n A) (Iℕ.lower m≤n op) sA
            List.∣  List.return sA where

    goal = Parser A ⟶ □ Parser (A → A → A) ⟶ Parser A

    rest : [ □ goal ⟶ Parser A ⟶ □ Parser (A → A → A) ⟶
             Success A ⟶ List ∘ Success A ]
    rest rec A op sA@(a ^ m<n , s) = runParser (call op m<n) ≤-refl s List.>>=
          λ sOp → let (f ^ p<m , s′) = sOp ; .p<n : _ < _; p<n = <-trans p<m m<n in
          let rec′ = call rec p<n (lower (<⇒≤ p<n) A) (Iℕ.lower (<⇒≤ p<n) op) in
          lift (<⇒≤ p<n) ∘ Success.map (f a $_) List.<$> runParser rec′ ≤-refl s′

  head+tail : [ Parser A ⟶ □ Parser A ⟶ Parser (List⁺ A) ]
  head+tail hd tl = NonEmpty.reverse
                <$> (iterate (NonEmpty.[_] <$> hd) (Iℕ.map (NonEmpty._∷⁺_ <$>_) tl))

  list⁺ : [ Parser A ⟶ Parser (List⁺ A) ]
  list⁺ pA = head+tail pA (box pA)
\end{code}
