open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional

module STRIPS.Core.Goals where
  open import STRIPS.Core.Conditions

  record Goal : Set where
    field
      pos : List Condition
      neg : List Condition

  variable
    g g₁ g₂ : Goal

  WfGoal : Goal → Set
  WfGoal G = (∀ g → g ∈ (Goal.pos G) → g ∉ (Goal.neg G)) × (∀ g → g ∈ (Goal.neg G) → g ∉ (Goal.pos G))
  