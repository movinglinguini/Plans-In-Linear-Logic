{-
  Instantiates ADJ Logic with modes, a preorder on modes, a decidable preorder on modes, and a base type
  to construct propositions from.
-}
open import Data.List using (List) renaming(_∷_ to _,_; [] to ∅)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊇_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary
open import Data.Nat
open import Data.Bool hiding (_≟_)

module ADJ.Core (TermAtom : Set) where
  open import Syntax.Core TermAtom
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
    subst : Prop → Term → Prop
    subst (` v[ p , b ]) t = {!   !}
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

  open import Logic.Adjoint Proposition TermAtom subst public
