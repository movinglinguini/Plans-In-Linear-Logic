open import Data.List
open import Relation.Binary.Definitions using (DecidableEquality)

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
      _≟ᶜ_ : DecidableEquality Condition

