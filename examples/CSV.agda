module CSV where

open import Text.Parser
open import Data.Char using (Char)

import Data.List as L
open L using (List; _∷_; []; [_])

import Data.List.NonEmpty as L+
open L+ using (_∷_) renaming (List⁺ to List+; [_] to [_]+)

open import Function using (_$_; _∘_; id)

import Data.Maybe as M
open M using (Maybe; just; nothing)

import Data.String as S
open S using (String)


open import Relation.Unary using (IUniversal)

private
  -- a helpful combinator that allows for failed parses as long as the
  -- separators are present
  -- e.g.
  -- _ : "a,,a" ∈ (char 'a' sepBy comma)
  -- _ = ((just 'a') ∷ nothing ∷ just 'a' ∷ []) !

  -- _ : "a" ∈ (char 'a' sepBy comma)
  -- _ = ((just 'a') ∷ []) !

  -- _ : ",,," ∈ (char 'a' sepBy comma)
  -- _ = nothing ∷ nothing ∷ nothing ∷ nothing ∷ [] !

  _sepBy_ : ∀ {A B} → ∀[ Parser A ⇒ Parser B ⇒ Parser (List+ (Maybe A)) ]
  pa sepBy pb =
    (uncurry L+._⁺∷ʳ_) <$> (list⁺ (pa <?& pb) <&?> box pa)
    <|> ([_]+ ∘ just <$> pa)
    where open import Data.Product using (uncurry)


  -- some useful converters
  List+→String : List+ Char → String
  List+→String = S.fromList ∘ L+.toList

  List+→List : {A : Set} → Maybe (List+ A) → List A
  List+→List (just (head ∷ tail)) = head ∷ tail
  List+→List nothing = []


  -- a few new parsers
  comma : ∀[ Parser Char ]
  comma = char ','

  newline : ∀[ Parser Char ]
  newline = char '\n'

  doublequote : ∀[ Parser Char ]
  doublequote = char '\"'

  -- doubled double-quotes allow you to insert double-quotes inside an entry
  double-doublequote : ∀[ Parser Char ]
  double-doublequote = doublequote &> box doublequote


  -- quoted CSV entries can contain any characters as long as they are
  -- surrounded by double quotes
  quoted : ∀[ Parser String ]
  quoted =
    List+→String
    <$>
      between
        doublequote
        (box doublequote)
        (box ∘ list⁺ $ double-doublequote <|> anyCharBut '\"')


  -- unquoted entries cannot contain newlines, commas, or quotes
  unquoted : ∀[ Parser String ]
  unquoted =
    List+→String
    <$>
      head+tail
        (noneOf ('\n' ∷ ',' ∷ '\"' ∷ []))
        (box $ noneOf ('\n' ∷ ',' ∷ []))


  -- a CSV entry is either quoted or unquoted.
  entry : ∀[ Parser String ]
  entry = quoted <|> unquoted


  -- a CSV line is one or several entries separated by commas.
  csvline : ∀[ Parser (List+ String) ]
  csvline = L+.map (M.fromMaybe "") <$> entry sepBy comma


-- a CSV document is one or several CSV lines.
csv : ∀[ Parser (List+ (List String)) ]
csv = L+.map List+→List <$> csvline sepBy newline


module Test where
  open import Data.Unit using (tt)
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  _ : "a,,a" ∈ (char 'a' sepBy comma)
  _ = ((just 'a') ∷ nothing ∷ just 'a' ∷ []) !

  _ : "a" ∈ (char 'a' sepBy comma)
  _ = ((just 'a') ∷ []) !

  _ : ",,," ∈ (char 'a' sepBy comma)
  _ = nothing ∷ nothing ∷ nothing ∷ nothing ∷ [] !

  _ : "\n" ∈ csv
  _ =  [] ∷ ([] ∷ []) !

  _ : ",\n" ∈ csv
  _ = ("" ∷ "" ∷ []) ∷ ([] ∷ []) !

  _ : "" ∉ csv
  _ = tt

  _ : "," ∈ csv
  _ = (("" ∷ "" ∷ []) ∷ []) !

  _ : ",hello,world,,\n" ∈ csv 
  _ = (("" ∷ "hello" ∷ "world" ∷ "" ∷ "" ∷ []) ∷ [] ∷ []) !

  _ : "\" \"\"hello\"\"\",world\n" ∈ csv
  _ = (" \"hello\"" ∷ "world" ∷ []) ∷ [] ∷ [] !

  _ : "\"well hello\",\"worldly \"\"world\"\"\"\n" ∈ csv
  _ = ("well hello" ∷ "worldly \"world\"" ∷ []) ∷ [] ∷ [] !

  _ : "\" hello,world\"" ∈ csv
  _ = ((" hello,world" ∷ []) ∷ []) !

  _ : "\" hello,world\"" ∈ csv
  _ = (" hello,world" ∷ []) ∷ [] !

  _ : "\" hello,world\", hello, world" ∈ csv
  _ = (" hello,world" ∷ " hello" ∷ " world" ∷ []) ∷ [] !

