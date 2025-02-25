open import Data.List
open import Data.Product
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List.Membership.Propositional

module STRIPS.Problem where
  open import STRIPS.Core.Common public
  open import STRIPS.Core.Terms public
  open import STRIPS.Core.Conditions public
  open import STRIPS.Core.Operators public
  open import STRIPS.Core.Goals public
  open import STRIPS.Core.Plans public

  record PlanProblem : Set where
    field
      terms : List Term
      conditions : List Condition
      initialState : List Condition
      operators : List Operator
      goals : Goal

  {---------------
  - Well-formedness criteria
  ----------------}
  WfState : List Condition → PlanProblem → Set
  WfState S P = (∀ i → i ∈ S → i ∈ (PlanProblem.conditions P))

  WfProblem : PlanProblem → Set
  WfProblem P = (WfGoal (PlanProblem.goals P)) -- Goals must be well-formed
    × (WfState (PlanProblem.initialState P) P) -- Problem initial state must be a subset of the problem conditions
    × (∀ g → g ∈ (Goal.pos (PlanProblem.goals P)) → g ∈ (PlanProblem.conditions P)) -- Goal conditions must be a subset of problem conditions 
    × (∀ g → g ∈ (Goal.neg (PlanProblem.goals P)) → g ∈ (PlanProblem.conditions P))
