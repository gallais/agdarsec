{-# OPTIONS --without-K --safe #-}

open import Level
open import Data.Unit
open import Data.Bool
open import Data.Char          as Char
open import Data.Char.Unsafe
open import Data.List          as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Maybe         as Maybe
open import Data.Product       as Prod
open import Data.String.Base   as String using (String)
open import Data.These         as These

open import Function

open import Text.Parser.Position as Pos using (Position)

module Text.Lexer
  -- Our lexer is parametrised over the type of tokens
  {t} {Tok : Set t}
  -- We start with an association list between
  -- * keywords (as Strings)
  -- * keywords (as token values)
  (keywords : List⁺ (String × Tok))
  -- Some characters are special: they are separators, breaking a string into
  -- a list of tokens. Some are associated to a token value (e.g. parentheses)
  -- others are not (e.g. space)
  (breaking : Char → ∃ λ b → if b then Maybe Tok else Lift _ ⊤)
  -- Finally, strings which are not decoded as keywords are coerced using a
  -- function to token values.
  (default  : String → Tok)
  where

  Result : Set _
  Result = List (Position × Tok)

  tokenize : String → Result
  tokenize = start Pos.start ∘′ String.toList where

   mutual

    -- We build a trie from the association list so that we may easily compute
    -- the successive derivatives obtained by eating the characters one by one
    Keywords : Set _
    Keywords = List (List Char × Tok)

    init : Keywords
    init = List.map (Prod.map₁ String.toList) $ List⁺.toList $ keywords

    read : Char → Keywords → Keywords
    read t = List.mapMaybe $ λ where
      (c ∷ cs , tok) → if c == t then just (cs , tok) else nothing
      _ → nothing

    value : Keywords → Maybe Tok
    value ks = List.head $ flip List.mapMaybe ks $ λ where
      ([] , k) → just k
      _ → nothing

    -- Kickstart the tokeniser with an empty accumulator and the initial trie.
    start : Position → List Char → Result
    start p = loop (p , []) init p

    -- The main loop
    loop :
      (acc  : Position × List Char) → -- start position & chars read so far in this token
      (toks : Keywords)             → -- keyword candidates left at this point
      (pos : Position)              → -- current position in the input string
      (input : List Char)           → -- list of chars to tokenize
      Result
    -- Empty input: finish up, check whether we have a non-empty accumulator
    loop acc toks pos []         = push acc []
    -- At least one character
    loop acc toks pos (c ∷ cs)   = case breaking c of λ where
      -- if we are supposed to break on this character, we do
      (true , m)  → push acc $ break pos m $ start (Pos.update c pos) cs
      -- otherwise we see whether reading it leads to a recognized keyword
      (false , _) → let toks' = read c toks in case value toks' of λ where
        -- if so we can forget about the current accumulator and restart
        -- the tokenizer on the rest of the input
        (just k) → (proj₁ acc , k) ∷ start (Pos.update c pos) cs
        -- otherwise we record the character we read in the accumulator,
        -- and keep going with the derivative of the map of keyword candidates
        -- and the rest of the input
        nothing  → loop (Prod.map₂ (c ∷_) acc) toks' (Pos.update c pos) cs

    -- Grab the accumulator and, unless it is empty, push it on top of the
    -- decoded list of tokens
    push : (Position × List Char) → Result → Result
    push (pos , []) ts = ts
    push (pos , cs) ts = (pos , default (String.fromList (List.reverse cs))) ∷ ts

    -- The action corresponding to a breaking character: we only push something
    -- if the breaking character is associated to a token
    break : Position → Maybe Tok → Result → Result
    break pos (just tok) rs = (pos , tok) ∷ rs
    break pos nothing    rs = rs
