-- Example taken from parsec's documentation
-- https://hackage.haskell.org/package/parsec-3.1.11/docs/Text-Parsec-Combinator.html#v:chainl1

module Text.Parser.Examples.Expr where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.List.Base as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.List.Sized.Interface
open import Data.Maybe
open import Data.Product
open import Function
import Induction.Nat.Strong as INS

open import Text.Parser.Examples.Base
open import Text.Parser.Examples.Identifier
open import Text.Parser.Examples.Decimal

data Expr : Set where
  Var     : Char → Expr
  Lit     : ℕ → Expr
  Add Sub : Expr → Expr → Expr
  Mul Div : Expr → Expr → Expr

module _ {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}} where

 record PExpr (n : ℕ) : Set where
   field pvar : Parser Char Chars Maybe Expr n
         plit : Parser Char Chars Maybe Expr n
         pfac : Parser Char Chars Maybe Expr n
         pexp : Parser Char Chars Maybe Expr n
 open PExpr

 pExpr : [ PExpr ]
 pExpr = fix PExpr $ λ rec →
         let factor = parens (INS.map pexp rec) <|> var <|> lit
             term   = chainl1 factor $ return mulop
             expr   = chainl1 term   $ return addop
         in record { pvar = var
                   ; plit = lit
                   ; pfac = factor
                   ; pexp = expr }


  module Details where

    var : [ Parser Char Chars Maybe Expr ]
    lit : [ Parser Char Chars Maybe Expr ]

    var = Var <$> alpha
    lit = Lit <$> decimal

    addop : [ Parser Char Chars Maybe (Expr → Expr → Expr) ]
    mulop : [ Parser Char Chars Maybe (Expr → Expr → Expr) ]

    addop = withSpaces (Add <$ char '+' <|> Sub <$ char '-')
    mulop = withSpaces (Mul <$ char '*' <|> Div <$ char '/')


 Expr′ : [ Parser Char Chars Maybe Expr ]
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
