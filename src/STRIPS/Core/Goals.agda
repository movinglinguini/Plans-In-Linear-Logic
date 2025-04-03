open import Data.Product
open import Data.Nat
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.Any
open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Bool
open import Data.Maybe
open import Relation.Nullary.Decidable

open import STRIPS.Core.Common

module STRIPS.Core.Goals where
  open import STRIPS.Core.Conditions

  -- A well-formed goal is one where all its conditions are in the problem condition vector.
  
  data Goals : ∀ { n } ( gs : ConditionConfiguration ) → ( ℂ : Vec GroundCondition n ) → Set where
    wf/goal/z : ∀ { n } { ℂ : Vec GroundCondition n } → Goals [] ℂ

    wf/goal/s : ∀ { n g gs } { ℂ : Vec GroundCondition n } 
      → Goals gs ℂ → (wfcond : (proj₁ g) ∈ ℂ)
        ------------------------------------
      → Goals (g ∷ gs) ℂ
 

  -- Example
  private
    ℂ : Vec GroundCondition 2
    ℂ = (record { label = "cond-1" ; terms = [] }) ∷ ((record { label = "cond-2" ; terms = [] }) ∷ [])

    gs : ConditionConfiguration
    gs = ((record { label = "cond-2" ; terms = [] }) , false) ∷ (((record { label = "cond-1" ; terms = [] }) , true) ∷ [])

    goals : Goals gs ℂ
    goals = wf/goal/s (wf/goal/s wf/goal/z (here refl)) (there (here refl))
  
  open import Data.Vec.Membership.DecPropositional { A = GroundCondition } (_≟ᶜ_)
  -- Build goals
  maybeGoal : ∀ { n } → (gs : ConditionConfiguration) → (ℂ : Vec GroundCondition n) → Maybe (Goals gs ℂ)
  maybeGoal [] ℂ = just wf/goal/z 
  maybeGoal (g ∷ gs) ℂ with (proj₁ g) ∈? ℂ
  ... | no ¬p = nothing
  ... | yes p₁ with maybeGoal gs ℂ
  ...   | nothing = nothing
  ...   | just p₂ = just (wf/goal/s p₂ p₁) 