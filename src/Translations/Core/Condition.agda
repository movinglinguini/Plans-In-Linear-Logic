open import Data.Vec hiding (length)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.String hiding (map ; length ; fromList)

module Translations.Core.Condition where
  open import STRIPS.Problem renaming (Term to STRIPSTerm)
  open import Translations.Core.Term
  open import Logic.Core.Terms TermAtom renaming (Term to AdjointTerm)

  record TCondition (Scope : ℕ) : Set where
    field
      { arity } : ℕ
      label : String
      terms : Vec (AdjointTerm Scope) arity

  -- This form of translC lifts the given condition to a higher scope.
  -- Most cases will just need regular old translC.
  translC′ : ∀ { o } (n : ℕ) → o Data.Nat.≤ n → Condition o → TCondition n   
  translC′ s o≤n record { label = label ; terms = terms } = record { label = label ; terms = translTs s o≤n (fromList terms) } 
  
  -- Trivial form of translC that translates a condition and retains the same scope.
  -- This will be very useful for translating most things.
  translC : ∀ { o } → Condition o → TCondition o
  translC {o} C = translC′ o ≤-refl C 
