open import Data.List
open import Relation.Binary.Definitions using (DecidableEquality)

module STRIPS.Problem (TermAtom : Set) where
  open import STRIPS.Core.Terms TermAtom public
  open import STRIPS.Core.Conditions TermAtom public
  open import STRIPS.Core.Operators TermAtom public
  open import STRIPS.Core.Goals TermAtom public

  record PlanProblem : Set where
    field
      terms : List Term
      conditions : List Condition
      initialState : List Condition
      operators : List Operator
      goals : Goal
      _≟ᶜ_ : DecidableEquality Condition

  variable
    𝕋 : List Term
    ℙ : List Condition
    𝕀 : List Condition
    𝕆 : List Operator
    𝔾 : Goal
