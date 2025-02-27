open import Data.List
open import Data.Vec hiding (foldr)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit
-- open import Data.List.Membership.DecPropositional
open import Data.List.Membership.Propositional

module STRIPS.Core.Common where
  open import STRIPS.Core.Conditions

  {- Satisfaction of conditions -}

  -- Boolean satisfaction: a condition satisfies a pair of lists of conditions if
  -- 1. all of the left part of the pair (the positive side) can be found in the condition
  -- 2. none of the right part of the pair (the negative side) can be found in the condition
  satᵇ : List (Condition 0) → (List (Condition 0)) × (List (Condition 0)) → Bool
  satᵇ C ⟨ G⁺ , G⁻ ⟩ = (allIn C G⁺) ∧ (noneIn C G⁻)
    where
      allIn : List (Condition 0) → List (Condition 0) → Bool
      allIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (x ∈ᶜᵇ ℂ₁)) true ℂ₂

      noneIn : List (Condition 0) → List (Condition 0) → Bool
      noneIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (not (x ∈ᶜᵇ ℂ₁))) true ℂ₂ 


  -- Propositional satisfaction: Similar to above, but we use propositional list membership.
  sat : List (Condition 0) → (List (Condition 0)) × (List (Condition 0)) → Set
  sat 𝕊 𝔾 = (∀ p → p ∈ proj₁ 𝔾 → p ∈ 𝕊) × (∀ p → p ∈ proj₂ 𝔾 → p ∉ 𝕊)

  private
    conds : List (Condition 0)
    conds = (record { name = "cond-1" ; terms = [] }) ∷ (record { name = "cond-2" ; terms = [] }) ∷ []

    goal1 : (List (Condition 0)) × (List (Condition 0))
    goal1 = ⟨ record { name = "cond-1" ; terms = [] } ∷ [] , [] ⟩

    goal2 : (List (Condition 0)) × (List (Condition 0))
    goal2 = ⟨ record { name = "cond-1" ; terms = [] } ∷ [] , record { name = "cond-2" ; terms = [] } ∷ [] ⟩

    _ : (satᵇ conds goal1) ≡ true
    _ = refl

    _ : (satᵇ conds goal2) ≡ false
    _ = refl

