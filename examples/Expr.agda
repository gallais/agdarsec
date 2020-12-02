-- Example taken from parsec's documentation
-- https://hackage.haskell.org/package/parsec-3.1.11/docs/Text-Parsec-Combinator.html#v:chainl1

module Expr where


import Level
open import Level.Bounded

open import Data.Char using (Char)
open import Data.List.Base as List using ()
open import Data.List.NonEmpty as List⁺ using ()
open import Data.Nat.Base using (ℕ)
import Data.List.Sized.Interface
open import Data.Maybe using ()
open import Data.Product
open import Function.Base
import Induction.Nat.Strong as INS

open import Base Level.zero
open import Identifier

data Expr : Set where
  Var     : Char → Expr
  Lit     : ℕ → Expr
  Add Sub : Expr → Expr → Expr
  Mul Div : Expr → Expr → Expr

record PExpr (P : Parameters Level.zero) (n : ℕ) : Set where
  field pvar : Parser P [ Expr ] n
        plit : Parser P [ Expr ] n
        pfac : Parser P [ Expr ] n
        pexp : Parser P [ Expr ] n
open PExpr

pExpr : ∀[ PExpr chars ]
pExpr = fix (PExpr chars) $ λ rec →
        let factor = parens (INS.map pexp rec) <|> var <|> lit
            term   = chainl1 factor $ box mulop
            expr   = chainl1 term   $ box addop
        in record { pvar = var
                  ; plit = lit
                  ; pfac = factor
                  ; pexp = expr }


 module Details where

   var : ∀[ Parser chars [ Expr ] ]
   lit : ∀[ Parser chars [ Expr ] ]

   var = Var <$> alpha
   lit = Lit <$> decimalℕ

   addop : ∀[ Parser chars ([ Expr ] ⟶ [ Expr ] ⟶ [ Expr ]) ]
   mulop : ∀[ Parser chars ([ Expr ] ⟶ [ Expr ] ⟶ [ Expr ]) ]

   addop = withSpaces (Add <$ char '+' <|> Sub <$ char '-')
   mulop = withSpaces (Mul <$ char '*' <|> Div <$ char '/')


Expr′ : ∀[ Parser chars [ Expr ] ]
Expr′ = pexp pExpr

-- tests

_ : "x+y+z" ∈ Expr′
_ = Add (Add (Var 'x') (Var 'y')) (Var 'z') !

_ : "x + y + z" ∈ Expr′
_ = Add (Add (Var 'x') (Var 'y')) (Var 'z') !

_ : "x+y*z+t" ∈ Expr′
_ = Add (Add (Var 'x') (Mul (Var 'y') (Var 'z'))) (Var 't') !

_ : "(x+y)*z*t+u" ∈ Expr′
_ = Add (Mul (Mul (Add (Var 'x') (Var 'y')) (Var 'z')) (Var 't')) (Var 'u') !

_ : "10*(x+5*y)+z*7" ∈ Expr′
_ = Add (Mul (Lit 10) (Add (Var 'x') (Mul (Lit 5) (Var 'y')))) (Mul (Var 'z') (Lit 7)) !
