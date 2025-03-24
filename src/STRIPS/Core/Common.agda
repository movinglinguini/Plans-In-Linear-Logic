open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Product

open import STRIPS.Core.Conditions

module STRIPS.Core.Common where
  -- Gets just the negatives from a condition configuration
  getNegatives : ∀ { s : ℕ } → List ((Condition s) × Bool) → List (Condition s)
  getNegatives [] = [] 
  getNegatives ((fst , false) ∷ ccs) = fst ∷ getNegatives ccs 
  getNegatives ((fst , true) ∷ ccs) = getNegatives ccs

  -- Gets just the positives from a condition configuration
  getPositives : ∀ { s : ℕ } → List ((Condition s) × Bool) → List (Condition s)
  getPositives [] = [] 
  getPositives ((fst , true) ∷ ccs) = fst ∷ getPositives ccs 
  getPositives ((fst , false) ∷ ccs) = getPositives ccs