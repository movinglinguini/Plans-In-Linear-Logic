open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Nat

module STRIPS.Core.Goals where
  open import STRIPS.Core.Conditions

  record Goal : Set where
    field
      pos : List (Condition 0)
      neg : List (Condition 0)

  WfGoal : Goal → Set
  WfGoal G = (∀ g → g ∈ (Goal.pos G) → g ∉ (Goal.neg G)) × (∀ g → g ∈ (Goal.neg G) → g ∉ (Goal.pos G))
  