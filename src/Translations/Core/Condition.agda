open import Data.Vec
open import Data.Nat
open import Data.String hiding (map)

module Translations.Core.Condition where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Term
  open import Logic.Core.Terms TermAtom

  record TCondition  : Set where
    field
      { arity } : ℕ
      name : String
      terms : Vec Term arity

  translC : ∀ { s } → Condition s → TCondition
  translC record { name = name ; terms = terms } = record { name = name ; terms = translTs terms } 