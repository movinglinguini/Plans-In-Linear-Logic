open import Data.String
open import Data.List 
open import Data.Vec
open import Data.Fin

module Translations.Core.Term where
  open import STRIPS.Problem renaming (Term to STRIPSTerm)
  open import Logic.Core.Terms TermAtom renaming (Term to ADJTerm)
  
  translT : ∀ { s } → STRIPSTerm s → ADJTerm 
  translT (const x) = const x
  translT (var x) = var (toℕ x)

  translTs : ∀ { s } (T : List (STRIPSTerm s)) → Vec ADJTerm (Data.List.length T)
  translTs [] = []
  translTs (x ∷ T) = translT x ∷ translTs T
