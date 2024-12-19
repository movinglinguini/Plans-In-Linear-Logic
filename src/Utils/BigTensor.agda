open import Data.List

module Utils.BigTensor (U : Set) where
  open import ADJ.Core U

  ⨂_ : List (Prop Linear) → Prop Linear
  ⨂ [] = 𝟙
  ⨂ (x ∷ xs) = x ⊗ (⨂ xs)