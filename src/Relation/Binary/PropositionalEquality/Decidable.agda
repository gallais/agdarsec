{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.Decidable where

open import Relation.Binary.PropositionalEquality.Decidable.Core public

open import Data.Char as C using (Char)
open import Data.String as S using (String)

instance

  decide-char : DecidableEquality Char
  decide-char .decide = C._≟_

  decide-string : DecidableEquality String
  decide-string .decide = S._≟_
