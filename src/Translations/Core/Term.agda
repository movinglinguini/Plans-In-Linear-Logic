open import Data.String
open import Data.List 
open import Data.Vec
open import Data.Fin
open import Data.Nat

module Translations.Core.Term where
  open import STRIPS.Problem renaming (Term to STRIPSTerm)
  open import Logic.Core.Terms TermAtom renaming (Term to ADJTerm)
  
  {-
    Translates a STRIPS term from one scope to an Adjoint Term of a new scope.
    For variable terms, we only allow injecting them into higher scopes.
  -}
  translT : ∀ { o } (n : ℕ) → o Data.Nat.≤ n  → STRIPSTerm o → ADJTerm n
  translT _ _ (const x) = const x
  translT n o≤n (var x) = var (inject≤ x o≤n)

  -- STRIPS Terms are generally held in lists in the STRIPS side, so we translate over
  -- lists
  translTs : ∀ { o } (n : ℕ) → o Data.Nat.≤ n → (ts : List (STRIPSTerm o)) → Vec (ADJTerm n) (Data.List.length ts)
  translTs _ _ [] = []
  translTs n o≤n (t ∷ ts) = (translT n o≤n t) ∷ (translTs n o≤n ts)

 