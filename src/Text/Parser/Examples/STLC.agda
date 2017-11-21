module Text.Parser.Examples.STLC where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.List.Base as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.List.Sized.Interface
open import Data.Maybe
open import Data.Product
import Induction.Nat.Strong as INS
open import Function

open import Text.Parser.Examples.Base
open import Text.Parser.Examples.Identifier
open import Text.Parser.Numbers

data Type : Set where
  `κ   : ℕ → Type
  _`→_ : Type → Type → Type

module _ {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}} where

 Type′ : [ Parser Char Chars Maybe Type ]
 Type′ = fix _ $ λ rec → chainr1 (`κ <$> decimalℕ <|> parens rec)
                                 (box $ _`→_ <$ withSpaces (char '→'))

_ : "1 → (2 → 3) → 4" ∈ Type′
_ = `κ 1 `→ ((`κ 2 `→ `κ 3) `→ `κ 4) !

mutual

  data Val : Set where
    Lam : Identifier → Val → Val
    Emb : Neu → Val

  data Neu : Set where
    Var : Identifier → Neu
    Cut : Val → Type → Neu
    App : Neu → Val → Neu

module _ {Chars : ℕ → Set} {{𝕊 : Sized Char Chars}} where

 record Language (n : ℕ) : Set where
   field pVal : Parser Char Chars Maybe Val n
         pNeu : Parser Char Chars Maybe Neu n
 open Language

 language : [ Language ]
 language = fix Language $ λ rec →
             let □val = INS.map pVal rec
                 cut  = uncurry Cut <$> (char '(' &> □val
                               <& box (withSpaces (char ':'))
                               <&> box Type′
                               <& box (char ')'))
                 neu  = hchainl (var <|> cut) (box (App <$ space)) □val
                 val  = uncurry Lam <$> (char 'λ' &> box (withSpaces identifier)
                                    <&> box ((char '.')
                                     &> □val))
                        <|> Emb <$> neu
             in record { pVal = val ; pNeu = neu }

   where

    var : [ Parser Char Chars Maybe Neu ]
    var = Var <$> identifier


 Val′ : [ Parser Char Chars Maybe Val ]
 Val′ = pVal language

-- tests

_ : "λx.x" ∈ Val′
_ = Lam (mkIdentifier ('x' ∷ []))
        (Emb (Var (mkIdentifier ('x' ∷ [])))) !

_ : "λx.λy.x y" ∈ Val′
_ = Lam (mkIdentifier ('x' ∷ []))
   (Lam (mkIdentifier ('y' ∷ []))
   (Emb (App (Var (mkIdentifier ('x' ∷ [])))
             (Emb (Var (mkIdentifier ('y' ∷ []))))))) !

_ : "λx.(λx.x : 1 → 1) x" ∈ Val′
_ = Lam (mkIdentifier ('x' ∷ []))
    (Emb (App
              (Cut (Lam (mkIdentifier ('x' ∷ []))
                        (Emb (Var (mkIdentifier ('x' ∷ [])))))
                   (`κ 1 `→ `κ 1))
              (Emb (Var (mkIdentifier ('x' ∷ [])))))) !
