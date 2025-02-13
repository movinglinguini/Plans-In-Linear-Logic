{-
  Instantiates ADJ Logic with modes, a preorder on modes, a decidable preorder on modes, and a base type
  to construct propositions from.
-}
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Nat
open import Data.Vec
open import Data.Bool hiding (_≟_)

module ADJ.Core where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Translations
  open import Logic.Core.Props Proposition public
  open import Logic.Core.Terms TermAtom public
  open import Logic.Core.Modes public
  open import Logic.Core.Contexts Proposition TermAtom public

  -- private
  --   rebase : Prop → Prop
  --   rebase (` v[ x , true ]) = ` v[ x , true ]
  --   rebase (` v[ x , false ]) = ` v[ x , false ]
  --   rebase (` v[ x , var x₁ ]) with x₁
  --   ... | zero = ` v[ x , var zero ]
  --   ... | suc a = ` v[ x , var a ]
  --   rebase (P ⊸ P₁) = (rebase P) ⊸ (rebase P₁)
  --   rebase (P ⊗ P₁) = (rebase P) ⊗ (rebase P₁)
  --   rebase 𝟙 = 𝟙
  --   rebase ⊤ = ⊤
  --   rebase (P ⊕ P₁) = (rebase P) ⊕ (rebase P₁)
  --   rebase (P & P₁) = (rebase P) & (rebase P₁)
  --   rebase (↑[ x ][ x₁ ] P) = ↑[ x ][ x₁ ] (rebase P)
  --   rebase (↓[ x ][ x₁ ] P) = ↓[ x ][ x₁ ] (rebase P)
  --   rebase ∀[ P ] = ∀[ rebase P ]

  --   subst : Prop → Term → Prop
  --   subst (` v[ x , true ]) t = ` v[ x , true ]
  --   subst (` v[ x , false ]) t = ` v[ x , false ]
  --   subst (` v[ x , var x₁ ]) t with does (x₁ ≟ zero)
  --   ... | false = ` v[ x , var x₁ ]
  --   ... | true with t
  --   ... | term x₂ = ` v[ x , x₂ ]
  --   subst (P ⊸ P₁) t = rebase ((subst P t) ⊸ (subst P₁ t))
  --   subst (P ⊗ P₁) t = rebase ((subst P t) ⊗ (subst P₁ t))
  --   subst 𝟙 t = 𝟙
  --   subst ⊤ t = ⊤
  --   subst (P ⊕ P₁) t = rebase((subst P t) ⊕ (subst P₁ t))
  --   subst (P & P₁) t = rebase((subst P t) & (subst P₁ t))
  --   subst (↑[ x ][ x₁ ] P) t = rebase (↑[ x ][ x₁ ] (subst P t))
  --   subst (↓[ x ][ x₁ ] P) t = rebase (↓[ x ][ x₁ ] (subst P t))
  --   subst ∀[ ` A ] t = subst ( ` A ) t
  --   subst ∀[ P ⊸ P₁ ] t = subst (P ⊸ P₁) t
  --   subst ∀[ P ⊗ P₁ ] t = subst (P ⊗ P₁) t
  --   subst ∀[ 𝟙 ] t = 𝟙
  --   subst ∀[ ⊤ ] t = ⊤
  --   subst ∀[ P ⊕ P₁ ] t = subst (P ⊕ P₁) t
  --   subst ∀[ P & P₁ ] t = subst (P & P₁) t
  --   subst ∀[ ↑[ x ][ x₁ ] P ] t = ↑[ x ][ x₁ ] (subst P t)
  --   subst ∀[ ↓[ x ][ x₁ ] P ] t = ↓[ x ][ x₁ ] (subst P t)
  --   subst ∀[ ∀[ P ] ] t = ∀[ subst ∀[ P ] t ]
  private
    subst-TCondition-Terms : ∀ { n } → Vec Term n → Term → Vec Term n
    subst-TCondition-Terms [] t = []
    subst-TCondition-Terms (term x ∷ T) t = term x ∷ (subst-TCondition-Terms T t)
    subst-TCondition-Terms (var x ∷ T) t with x
    ... | zero = t ∷ subst-TCondition-Terms T t
    ... | suc x = var x ∷ subst-TCondition-Terms T t

    subst-TCondition : TCondition → Term → TCondition
    subst-TCondition record { name = name ; args = args } t = record { name = name ; args = (subst-TCondition-Terms args t) }

    subst : Prop → Term → Prop
    subst (` v[ p , b ]) t with b
    ... | term x = ` v[ (subst-TCondition p t) , (term x) ]
    ... | var x with x
    ...   | zero = ` v[ (subst-TCondition p t), t ]
    ...   | suc x = ` v[ (subst-TCondition p t) , var x ]
    subst (p₁ ⊸ p₂) t = (subst p₁ t) ⊸ (subst p₂ t)
    subst (p₁ ⊗ p₂) t = ((subst p₁ t)) ⊗ subst p₂ t
    subst 𝟙 t = 𝟙
    subst ⊤ t = ⊤
    subst (p₁ ⊕ p₂) t = subst p₁ t ⊕ subst p₂ t
    subst (p₁ & p₂) t = (subst p₁ t) & subst p₂ t
    subst (↑[ x ][ x₁ ] p) t = ↑[ x ][ x₁ ] (subst p t)
    subst (↓[ x ][ x₁ ] p) t = ↓[ x ][ x₁ ] (subst p t)
    subst ∀[ ∀[ p ] ] t = ∀[ subst ∀[ p ] t ]
    subst ∀[ p ] t = subst p t

    -- Test out substitution
    cond1 : TCondition
    cond1 = record { name = "cond-1" ; args = var 0 ∷ term "t1" ∷ [] }

    cond2 : TCondition
    cond2 = record { name = "cond-2" ; args = var 1 ∷ term "t2" ∷ [] }

    cond1trans : TCondition
    cond1trans = record { name = "cond-1" ; args = term "s1" ∷ term "t1" ∷ [] }

    cond2trans1 : TCondition
    cond2trans1 = record { name = "cond-2" ; args = var 0 ∷ term "t2" ∷ [] }

    prop1 : Prop
    prop1 = ∀[ ∀[ (` v[ cond1 , term "b1" ]) ⊸ (` v[ cond2 , var 0 ])  ]  ]

    _ : subst prop1 (term "s1") ≡ ∀[ (` v[ cond1trans , term "b1" ]) ⊸ (` v[ cond2trans1 , term "s1" ] ) ]
    _ = refl 

  open import Logic.Adjoint Proposition TermAtom subst public
