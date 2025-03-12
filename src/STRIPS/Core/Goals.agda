open import Data.Product
open import Data.Nat
open import Data.Vec
open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Bool

module STRIPS.Core.Goals where
  open import STRIPS.Core.Conditions

  -- record Goal (Size : ℕ) : Set where
  --   field
  --     { posSize } : Fin Size
  --     pos : Vec (Condition 0) (toℕ posSize)
  --     neg : Vec (Condition 0) (Size ∸ (toℕ posSize))

  -- sizeOf-Goal : ∀ { n } ( G : Goal n ) → ℕ
  -- sizeOf-Goal {n} G = (toℕ (Goal.posSize G)) + (n ∸ toℕ (Goal.posSize G))
  
  Goal = List (GroundCondition × Bool)

  getConditions-Goal : Goal → List GroundCondition
  getConditions-Goal [] = []
  getConditions-Goal (x ∷ 𝔾) = proj₁ x ∷ getConditions-Goal 𝔾

  getPositives-Goal : Goal → List GroundCondition
  getPositives-Goal [] = []
  getPositives-Goal ((fst , false) ∷ 𝔾) = getPositives-Goal 𝔾
  getPositives-Goal ((fst , true) ∷ 𝔾) = fst ∷ getPositives-Goal 𝔾

  getNegatives-Goal : Goal → List GroundCondition
  getNegatives-Goal [] = []
  getNegatives-Goal ((fst , false) ∷ 𝔾) = fst ∷ getNegatives-Goal 𝔾
  getNegatives-Goal ((fst , true) ∷ 𝔾) = getNegatives-Goal 𝔾

  sizeOf-Goal : Goal → ℕ
  sizeOf-Goal 𝔾 = Data.List.length (getPositives-Goal 𝔾) + Data.List.length (getNegatives-Goal 𝔾)

  -- WfGoal : Goal → Set
  -- WfGoal G = (∀ g → g ∈ (Goal.pos G) → g ∉ (Goal.neg G)) × (∀ g → g ∈ (Goal.neg G) → g ∉ (Goal.pos G))
  