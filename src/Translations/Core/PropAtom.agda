open import Translations.Core.Condition
open import STRIPS.Problem

module Translations.Core.PropAtom where
  open import Logic.Core.Terms TermAtom renaming (Term to AdjointTerm)
  -- We are ultimately translating Conditions into PropAtoms,
  -- which contain translated conditions (TCondition) + a truth value term.
  infix 10 v[_,_]
  data PropAtom : Set where
    v[_,_] : ∀ { s } → TCondition s → AdjointTerm s → PropAtom