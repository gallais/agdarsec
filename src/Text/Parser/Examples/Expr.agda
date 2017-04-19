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

open import Text.Parser.Examples.Base
open import Text.Parser.Examples.Identifier
open import Text.Parser.Examples.Decimal


data Expr : Set where
  Var     : Char → Expr
  Lit     : ℕ → Expr
  Add Sub : Expr → Expr → Expr
  Mul Div : Expr → Expr → Expr

module _ {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}} where

 Expr′ : [ Parser Char Chars Maybe Expr ]
 Expr′ = fix (Parser Char Chars Maybe Expr) $ λ rec →
         let var    = Var <$> alpha
             lit    = Lit <$> decimal
             addop  = withSpaces (Add <$ char '+' <|> Sub <$ char '-')
             mulop  = withSpaces (Mul <$ char '*' <|> Div <$ char '/')
             factor = parens rec <|> var <|> lit
             term   = chainl1 factor $ return mulop
             expr   = chainl1 term   $ return addop
         in expr


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
