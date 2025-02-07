open import Data.Vec
open import Data.Nat
open import Data.String hiding (map)

module Translations.Condition (TermAtom : Set) where
  open import STRIPS.Problem TermAtom hiding (Term)
  open import Translations.Term TermAtom
  open import Logic.Core.Terms TermAtom

  record TCondition : Set where
    field
      { argLength } : ℕ
      name : String
      args : Vec Term argLength

  translC : Condition → TCondition
  translC record { name = name ; args = args } = record { name = name ; args = map (λ t → translT t) args } 