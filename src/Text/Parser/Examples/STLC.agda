module Text.Parser.Examples.STLC where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.List.Base as List hiding ([_])
open import Data.List.NonEmpty as NonEmpty hiding ([_])
open import Data.Maybe
open import Data.Product
open import Function

open import Text.Parser.Examples.Base
open import Text.Parser.Examples.Identifier
open import Text.Parser.Examples.Decimal

data Type : Set where
  `κ   : ℕ → Type
  _`→_ : Type → Type → Type

Type′ : [ Parser Char Maybe Type ]
Type′ = fix _ $ λ rec → chainr1 (`κ <$> decimal <|> parens rec)
                                (return $ _`→_ <$ withSpaces (char '→'))

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

Val′ : [ Parser Char Maybe Val ]
Val′ = fix _ $ λ rec →
       let var = Var <$> identifier
           cut = uncurry Cut <$> (char '(' &> rec
                             <& return (withSpaces (char ':'))
                             <&> return Type′
                             <& return (char ')'))
           neu = hchainl (var <|> cut) (return (App <$ space)) rec
       in uncurry Lam <$> (char 'λ' &> return (withSpaces identifier)
                                   <&> return ((char '.')
                                    &> rec))
          <|> Emb <$> neu

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
