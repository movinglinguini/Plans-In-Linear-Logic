open import Data.Nat
open import Data.Bool
open import Data.String
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Relation.Nullary.Negation

module STRIPS.Core.Terms where
  TermAtom = String


  data Term : Set where
    term : TermAtom → Term
    var : ℕ → Term

  variable
    t t₁ t₂ x x₁ x₂ : Term

  {- Operations on terms -}
  isVarᵇ : Term → Bool
  isVarᵇ (term x) = false
  isVarᵇ (var x) = true

  isConstᵇ : Term → Bool
  isConstᵇ t = not (isVarᵇ t)

  isVar : ∀ (t : Term) → Set
  isVar t = T (isVarᵇ t)

  isConst : ∀ (t : Term) → Set
  isConst t = ¬ (isVar t)

  isConst? : ∀ (t : Term) → Dec (isConst t)
  isConst? (term x) = yes (λ ())
  isConst? (var x) = no (λ x₁ → x₁ tt)

  isVar? : ∀ (t : Term) → Dec (isVar t)
  isVar? (term x) = no (λ ())
  isVar? (var x) = yes tt

  private
    _ : isVar (var 0) ≡ ⊤
    _ = refl
