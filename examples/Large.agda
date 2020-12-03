module Large where

import Level
open import Level.Bounded as Level≤
open import Base (Level.suc Level.zero)

open import Algebra
open import Data.Product as Product using (_,_; proj₁)
open import Data.List.Sized.Interface using ()
open import Function.Base using (_$_; _∘′_)

SmallMagma : Set≤ (Level.suc Level.zero)
level≤ SmallMagma = MkLevel≤ (Level.suc Level.zero)
theSet SmallMagma = Magma Level.zero Level.zero

data Expr (A : Set) : Set where
  Atom : A → Expr A
  Mult : Expr A → Expr A → Expr A

expr : ∀[ Parser chars (Σ SmallMagma λ m → ∀[ Parser chars ([ Magma.Carrier m ]) ])
        ⇒ Parser chars (Σ SmallMagma λ m → Expr (Magma.Carrier m)) ]
expr input =

  let expr : ((m , _) : theSet (Σ SmallMagma λ m → ∀[ Parser chars [ Magma.Carrier m ] ])) →
             ∀[ Parser chars (Σ SmallMagma λ m → Expr (Magma.Carrier m)) ]
      expr = λ (m , p) → (m ,_) <$> (fix (Parser chars [ Expr (Magma.Carrier m) ]) $ λ rec →
             let atom : Parser chars [ Expr _ ] _
                 atom = Atom <$> p <|> parens rec
             in chainr1 atom (box (withSpaces (Mult <$ char '*'))))
  in input >>= λ mp → box (expr mp)

open import Data.Nat.Base using (ℕ)
import Data.Nat.Properties as ℕₚ
import Data.Integer.Properties as ℤₚ

ℕorℤ : ∀[ Parser chars (Σ SmallMagma λ m → Expr (Magma.Carrier m)) ]
ℕorℤ = expr $ ((ℕₚ.*-magma , (λ {x} → decimalℕ)) <$ text "ℕ: ")
          <|> ((ℤₚ.*-magma , (λ {x} → decimalℤ)) <$ text "ℤ: ")

nat : "ℕ: (2 * (1)) * 3" ∈ ℕorℤ
nat = ℕₚ.*-magma , Mult (Mult (Atom 2) (Atom 1)) (Atom 3) !

open import Data.Integer.Base using (+_)

int : "ℤ: (2 * (1)) * 3" ∈ ℕorℤ
int = ℤₚ.*-magma , Mult (Mult (Atom (+ 2)) (Atom (+ 1))) (Atom (+ 3)) !
