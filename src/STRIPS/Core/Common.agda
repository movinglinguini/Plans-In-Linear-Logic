open import Data.List
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module STRIPS.Core.Common where
  open import STRIPS.Core.Conditions

  {- Satisfaction of conditions -}
  satᵇ : List Condition → (List Condition) × (List Condition) → Bool
  satᵇ ℂ ⟨ ℂ⁺ , ℂ⁻ ⟩ = (allIn ℂ ℂ⁺) ∧ (noneIn ℂ ℂ⁺)
    where
      allIn : List Condition → List Condition → Bool
      allIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (x ∈ᶜᵇ ℂ₁)) true ℂ₂

      noneIn : List Condition → List Condition → Bool
      noneIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (not (x ∈ᶜᵇ ℂ₁))) true ℂ₂ 

  sat : List Condition → (List Condition) × (List Condition) → Set
  sat ℂ 𝔾 = T (satᵇ ℂ 𝔾) 
