-- Example taken from parsec's documentation
-- https://hackage.haskell.org/package/parsec-3.1.11/docs/Text-Parsec-Combinator.html#v:chainl1

\begin{code}
module Text.Parser.Examples.Expr where

open import Data.Nat.Base
open import Data.Char.Base
open import Function

open import Relation.Unary.Indexed
open import Induction.Nat.Strong
open import Text.Parser.Combinators
open import Text.Parser.Char
open import Text.Parser.Examples.Decimal

mutual
\end{code}
%<*expr>
\begin{code}
 data Expr : Set where
   Emb  : Term → Expr
   Add  : Expr → Term → Expr
   Sub  : Expr → Term → Expr
\end{code}
%</expr>
%<*term>
\begin{code}
 data Term : Set where
   Emb  : Factor → Term
   Mul  : Term → Factor → Term
   Div  : Term → Factor → Term
\end{code}
%</term>
%<*factor>
\begin{code}
 data Factor : Set where
   Emb  : Expr → Factor
   Lit  : ℕ → Factor
\end{code}
%</factor>
%<*language>
\begin{code}
record Language (n : ℕ) : Set where
  field  expr    : Parser Expr n
         term    : Parser Term n
         factor  : Parser Factor n
\end{code}
%</language>
\begin{code}
open Language


\end{code}
%<*parser>
\begin{code}
language : [ Language ]
language =  fix Language $ λ rec →
  let  addop   = Add <$ char '+' <|> Sub <$ char '-'
       mulop   = Mul <$ char '*' <|> Div <$ char '/'
       factor  = Emb <$> parens (map expr rec) <|> Lit <$> decimal
       term    = hchainl (Emb <$> factor)  (box mulop) (box factor)
       expr    = hchainl (Emb <$> term)    (box addop) (box term)
  in record { expr = expr ; term = term ; factor = factor }
\end{code}
%</parser>
