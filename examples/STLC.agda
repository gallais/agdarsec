module STLC where

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Bool.Base
open import Data.Nat.Properties using (≤-refl)
open import Data.Char.Base
open import Data.String as String
open import Data.String.Unsafe as Str
open import Data.List.Base as List
open import Data.List.NonEmpty
open import Data.Vec as Vec
open import Data.Maybe.Base
open import Data.List.Sized.Interface
open import Data.Product
open import Induction.Nat.Strong as INS using (□_; fix)
open import Function

open import Relation.Nullary
open import Relation.Nullary.Decidable using (map′)
open import Relation.Unary as U renaming (_⇒_ to _⟶_)
open import Relation.Binary as B
open import Relation.Binary.PropositionalEquality

open import Text.Parser.Types
open import Text.Parser.Position
open import Text.Parser.Combinators
open import Text.Parser.Combinators.Numbers
open import Text.Parser.Monad

data Tok : Set where
  LAM ARR DOT COL : Tok
  LPAR RPAR : Tok
  ID : String → Tok

eqTok : B.Decidable {A = Tok} _≡_
eqTok LAM LAM = yes refl
eqTok LAM ARR = no (λ ())
eqTok LAM DOT = no (λ ())
eqTok LAM COL = no (λ ())
eqTok LAM LPAR = no (λ ())
eqTok LAM RPAR = no (λ ())
eqTok LAM (ID x) = no (λ ())
eqTok ARR LAM = no (λ ())
eqTok ARR ARR = yes refl
eqTok ARR DOT = no (λ ())
eqTok ARR COL = no (λ ())
eqTok ARR LPAR = no (λ ())
eqTok ARR RPAR = no (λ ())
eqTok ARR (ID x) = no (λ ())
eqTok DOT LAM = no (λ ())
eqTok DOT ARR = no (λ ())
eqTok DOT DOT = yes refl
eqTok DOT COL = no (λ ())
eqTok DOT LPAR = no (λ ())
eqTok DOT RPAR = no (λ ())
eqTok DOT (ID x) = no (λ ())
eqTok COL LAM = no (λ ())
eqTok COL ARR = no (λ ())
eqTok COL DOT = no (λ ())
eqTok COL COL = yes refl
eqTok COL LPAR = no (λ ())
eqTok COL RPAR = no (λ ())
eqTok COL (ID x) = no (λ ())
eqTok LPAR LAM = no (λ ())
eqTok LPAR ARR = no (λ ())
eqTok LPAR DOT = no (λ ())
eqTok LPAR COL = no (λ ())
eqTok LPAR LPAR = yes refl
eqTok LPAR RPAR = no (λ ())
eqTok LPAR (ID x) = no (λ ())
eqTok RPAR LAM = no (λ ())
eqTok RPAR ARR = no (λ ())
eqTok RPAR DOT = no (λ ())
eqTok RPAR COL = no (λ ())
eqTok RPAR LPAR = no (λ ())
eqTok RPAR RPAR = yes refl
eqTok RPAR (ID x) = no (λ ())
eqTok (ID x) LAM = no (λ ())
eqTok (ID x) ARR = no (λ ())
eqTok (ID x) DOT = no (λ ())
eqTok (ID x) COL = no (λ ())
eqTok (ID x) LPAR = no (λ ())
eqTok (ID x) RPAR = no (λ ())
eqTok (ID x) (ID y) = map′ (cong ID) (λ where refl → refl) (x Str.≟ y)

Token : Set
Token = Position × Tok

keywords : List⁺ (String × Tok)
keywords = ("→"   , ARR)
         ∷ ("λ"   , LAM)
         ∷ (":"   , COL)
         ∷ []

breaking : Char → ∃ λ b → if b then Maybe Tok else Lift _ ⊤
breaking c = case c of λ where
  '(' → true , just LPAR
  ')' → true , just RPAR
  '.' → true , just DOT
  c   → if isSpace c then true , nothing else false , _

open import Text.Lexer keywords breaking ID using (tokenize)

infixr 15 _`→_
data Type : Set where
  `κ   : String → Type
  _`→_ : Type → Type → Type

module ParserM = Agdarsec Position ⊥ (record { into = proj₁ })
open ParserM

instance
  _ = ParserM.monadZero
  _ = ParserM.monadPlus
  _ = ParserM.monad

P = ParserM.param Token (Vec Token) λ where (p , _) _ → Value (_ , p , [])

theTok : Tok → ∀[ Parser P Token ]
theTok t = maybeTok $ λ where
  tok@(p , t') → case eqTok t t' of λ where
    (yes eq) → just tok
    (no ¬eq) → nothing

parens : ∀ {A} → ∀[ □ Parser P A ⟶ Parser P A ]
parens □p = theTok LPAR &> □p <& box (theTok RPAR)

name : ∀[ Parser P String ]
name = maybeTok λ where (p , ID str) → just str; _ → nothing

type : ∀[ Parser P Type ]
type = fix _ $ λ rec →
  let varlike str = case String.toList str of λ where
        ('`' ∷ nm) → just (String.fromList nm)
        _ → nothing
  in chainr1 (`κ <$> guardM varlike name <|> parens rec)
             (box (_`→_ <$ theTok ARR))

open import Base using (Singleton; _!)

parse : ∀ {A} → ∀[ Parser P A ] → String → Set
parse p str = let input = Vec.fromList (tokenize str) in
  case runParser p ≤-refl input (start , []) of λ where
    (Value ((a ^ _ , _) , _)) → Singleton a
    _ → ⊥

_ : parse type "`a → (`b → `c) → `b"
_ = `κ "a" `→ (`κ "b" `→ `κ "c") `→ `κ "b" !

mutual

  data Val : Set where
    Lam : String → Val → Val
    Emb : Neu → Val

  data Neu : Set where
    Var : String → Neu
    Cut : Val → Type → Neu
    App : Neu → Val → Neu

record Language n : Set where
  field pVal : Parser P Val n
        pNeu : Parser P Neu n
open Language

language : ∀[ Language ]
language = fix Language $ λ rec →
  let □val = INS.map pVal rec
      □neu = INS.map pNeu rec
      var  = Var <$> guard (List.all isAlpha ∘′ String.toList) name
      cut  = (λ where ((v , _) , σ) → Cut v σ)
             <$> (theTok LPAR
              &> □val <&> box (theTok COL) <&> box (commit type)
              <& box (theTok RPAR))
      app  = flip App <$> ((Emb <$> var) <|> parens □val)
      neu  = iterate (var <|> cut <|> parens (INS.map commit □neu)) (box app)
      lam  = uncurry Lam
             <$> ((theTok LAM &> box name)
             <&> box (theTok DOT &> INS.map commit □val))
      val = lam <|> Emb <$> neu

  in record { pVal = val <|> parens (INS.map commit □val)
            ; pNeu = neu <|> parens (INS.map commit □neu)
            }

val : ∀[ Parser P Val ]
val = pVal language

-- tests

_ : parse val "λx.x"
_ = Lam "x" (Emb (Var "x")) !

_ : parse val "λx.λy.x y"
_ = Lam "x" (Lam "y" (Emb (App (Var "x") (Emb (Var "y"))))) !

_ : parse val "λx.(λx.x : `a → `a) x"
_ = Lam "x"
      (Emb (App (Cut (Lam "x" (Emb (Var "x"))) (`κ "a" `→ `κ "a"))
                (Emb (Var "x")))) !

_ : parse val "λg.λf.λa.g a (f a)"
_ = Lam "g" (Lam "f" (Lam "a"
     (Emb (App (App (Var "g") (Emb (Var "a")))
               (Emb (App (Var "f") (Emb (Var "a")))))))) !

_ : parse val "λg.λf.λa.(g a) (f a)"
_ = Lam "g" (Lam "f" (Lam "a"
     (Emb (App (App (Var "g") (Emb (Var "a")))
               (Emb (App (Var "f") (Emb (Var "a")))))))) !

_ : parse val "λg.λf.λa.((g) (a)) (f a))"
_ = Lam "g" (Lam "f" (Lam "a"
     (Emb (App (App (Var "g") (Emb (Var "a")))
               (Emb (App (Var "f") (Emb (Var "a")))))))) !
