open import Data.List
open import Data.Product
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List.Membership.Propositional

module STRIPS.Problem where
  {- Repackaging the other parts of the STRIPS encoding -}
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
      initialState : State
      operators : List Operator
      goals : Goal
