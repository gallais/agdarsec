module Relation.Binary.PropositionalEquality.Decidable where

open import Relation.Binary.PropositionalEquality.Decidable.Core public

open import Data.Char using (Char)
import Data.Char.Unsafe as C using (_≟_)
open import Data.String using (String)
import Data.String.Unsafe as S using (_≟_)

instance

  decide-char : DecidableEquality Char
  decide-char .decide = C._≟_

  decide-string : DecidableEquality String
  decide-string .decide = S._≟_
