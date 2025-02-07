open import Data.List

module STRIPS.Core.Goals where
  open import STRIPS.Core.Conditions

  record Goal : Set where
    field
      pos : List Condition
      neg : List Condition

  variable
    g g₁ g₂ : Goal

  data WFGoal : Goal → Set where
    wf/goal : Disjoint (Goal.pos g) (Goal.neg g)
      → WFGoal g