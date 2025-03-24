open import Data.List
open import Data.Vec hiding (foldr)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional

module STRIPS.Core.Sat where
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Goals

  {- Satisfaction of conditions -}

  -- Boolean satisfaction: a condition satisfies a pair of lists of conditions if
  -- 1. all of the left part of the pair (the positive side) can be found in the condition
  -- 2. none of the right part of the pair (the negative side) can be found in the condition
  satᵇ : List GroundCondition → (List (Condition 0)) × (List (Condition 0)) → Bool
  satᵇ C ⟨ G⁺ , G⁻ ⟩ = (allIn C G⁺) ∧ (noneIn C G⁻)
    where
      allIn : List (Condition 0) → List (Condition 0) → Bool
      allIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (x ∈ᶜᵇ ℂ₁)) true ℂ₂

      noneIn : List (Condition 0) → List (Condition 0) → Bool
      noneIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (not (x ∈ᶜᵇ ℂ₁))) true ℂ₂ 


  -- Propositional satisfaction: Similar to above, but we use propositional list membership.
  -- sat : List GroundCondition → (List (Condition 0)) × (List (Condition 0)) → Set
  -- sat 𝕊 𝔾 = T (satᵇ 𝕊 𝔾)

  -- sat′ : List GroundCondition → (List (Condition 0)) × (List (Condition 0)) → Set
  -- sat′ S G = (∀ g → g ∈ (proj₁ G) → g ∈ S) × (∀ g → g ∈ (proj₂ G) → g ∉ S)

  sat-Condition : List GroundCondition → (GroundCondition × Bool) → Set
  sat-Condition S ⟨ c , false ⟩ = c ∉ S
  sat-Condition S ⟨ c , true ⟩ = c ∈ S 

  sat : List GroundCondition → List (GroundCondition × Bool) → Set
  sat S cs = ∀ c → c ∈ cs → sat-Condition S c

  {-
    Properties of sat
  -}
  satg∷G⇒satG : ∀ { g G S } → sat S (g ∷ G) → sat S G
  satg∷G⇒satG sat = λ c z → sat c (there z)

  -- Testing out satisfaction
  private
    state : List GroundCondition
    state = (record { label = "cond-1" ; terms = [] }) ∷ (record { label = "cond-2" ; terms = [] }) ∷ []

    goal1 : (List (Condition 0)) × (List (Condition 0))
    goal1 = ⟨ record { label = "cond-1" ; terms = [] } ∷ [] , [] ⟩

    goal2 : (List (Condition 0)) × (List (Condition 0))
    goal2 = ⟨ record { label = "cond-1" ; terms = [] } ∷ [] , record { label = "cond-2" ; terms = [] } ∷ [] ⟩

    _ : (satᵇ state goal1) ≡ true
    _ = refl

    _ : (satᵇ state goal2) ≡ false
    _ = refl


