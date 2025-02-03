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

open import Plans.Domain

module ADJ.Core (domain : Domain) where
  open Domain domain
  
  open import Syntax.Core domain renaming (Term to BaseTerm)
  open import Logic.Core.Props Proposition public
  open import Logic.Core.Terms BaseTerm public
  open import Logic.Core.Modes public
  open import Logic.Core.Contexts Proposition BaseTerm public

  private
    rebase : Prop → Prop
    rebase (` v[ x , true ]) = ` v[ x , true ]
    rebase (` v[ x , false ]) = ` v[ x , false ]
    rebase (` v[ x , var x₁ ]) with x₁
    ... | zero = ` v[ x , var zero ]
    ... | suc a = ` v[ x , var a ]
    rebase (P ⊸ P₁) = (rebase P) ⊸ (rebase P₁)
    rebase (P ⊗ P₁) = (rebase P) ⊗ (rebase P₁)
    rebase 𝟙 = 𝟙
    rebase ⊤ = ⊤
    rebase (P ⊕ P₁) = (rebase P) ⊕ (rebase P₁)
    rebase (P & P₁) = (rebase P) & (rebase P₁)
    rebase (↑[ x ][ x₁ ] P) = ↑[ x ][ x₁ ] (rebase P)
    rebase (↓[ x ][ x₁ ] P) = ↓[ x ][ x₁ ] (rebase P)
    rebase ∀[ P ] = ∀[ rebase P ]

    subst : Prop → Term → Prop
    subst (` v[ x , true ]) t = ` v[ x , true ]
    subst (` v[ x , false ]) t = ` v[ x , false ]
    subst (` v[ x , var x₁ ]) t with does (x₁ ≟ zero)
    ... | false = ` v[ x , var x₁ ]
    ... | true with t
    ... | term x₂ = ` v[ x , x₂ ]
    subst (P ⊸ P₁) t = rebase ((subst P t) ⊸ (subst P₁ t))
    subst (P ⊗ P₁) t = rebase ((subst P t) ⊗ (subst P₁ t))
    subst 𝟙 t = 𝟙
    subst ⊤ t = ⊤
    subst (P ⊕ P₁) t = rebase((subst P t) ⊕ (subst P₁ t))
    subst (P & P₁) t = rebase((subst P t) & (subst P₁ t))
    subst (↑[ x ][ x₁ ] P) t = rebase (↑[ x ][ x₁ ] (subst P t))
    subst (↓[ x ][ x₁ ] P) t = rebase (↓[ x ][ x₁ ] (subst P t))
    subst ∀[ ` A ] t = subst ( ` A ) t
    subst ∀[ P ⊸ P₁ ] t = subst (P ⊸ P₁) t
    subst ∀[ P ⊗ P₁ ] t = subst (P ⊗ P₁) t
    subst ∀[ 𝟙 ] t = 𝟙
    subst ∀[ ⊤ ] t = ⊤
    subst ∀[ P ⊕ P₁ ] t = subst (P ⊕ P₁) t
    subst ∀[ P & P₁ ] t = subst (P & P₁) t
    subst ∀[ ↑[ x ][ x₁ ] P ] t = ↑[ x ][ x₁ ] (subst P t)
    subst ∀[ ↓[ x ][ x₁ ] P ] t = ↓[ x ][ x₁ ] (subst P t)
    subst ∀[ ∀[ P ] ] t = ∀[ subst ∀[ P ] t ]

  open import Logic.Adjoint Proposition BaseTerm subst public
  

  -- Testing substitution
  postulate
    p[t] : Predicate

  testProp : Prop
  testProp = ∀[ ∀[ (` v[ p[t] , var zero ]) ⊸ (` v[ p[t] , var 1 ]) ] ]

  _ : subst testProp (term true) ≡  ∀[ (` v[ p[t] , true ]) ⊸ (` v[ p[t] , var 0 ]) ]
  _ = refl

  _ : subst (subst testProp (term true)) (term false) ≡  (` v[ p[t] , true ]) ⊸ (` v[ p[t] , false ])
  _ = refl