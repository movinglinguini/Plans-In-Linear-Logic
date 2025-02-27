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

  {- 
    A PlanProblem is defined as a tuple ⟨ 𝕋 , ℙ , 𝕀 , 𝕆 , 𝔾 ⟩, where
      - 𝕋 is a set of terms
      - ℙ is a set of conditions
      - 𝕀 is a the initial state
      - 𝕆 is a set of operators
      - 𝔾 is the goal tuple
  -}
  record PlanProblem : Set where
    field
      terms : List (Term 0)
      conditions : List (Condition 0)
      initialState : List (Condition 0)
      operators : List Operator
      goals : Goal

  {---------------
  - Well-formedness criteria
  ----------------}
  -- WfState : List Condition → PlanProblem → Set
  -- WfState S P = (∀ i → i ∈ S → i ∈ (PlanProblem.conditions P))

  -- WfProblem : PlanProblem → Set
  -- WfProblem P = (WfGoal (PlanProblem.goals P)) -- Goals must be well-formed
  --   × (WfState (PlanProblem.initialState P) P) -- Problem initial state must be a subset of the problem conditions
  --   × (∀ g → g ∈ (Goal.pos (PlanProblem.goals P)) → g ∈ (PlanProblem.conditions P)) -- Goal conditions must be a subset of problem conditions 
  --   × (∀ g → g ∈ (Goal.neg (PlanProblem.goals P)) → g ∈ (PlanProblem.conditions P))
 