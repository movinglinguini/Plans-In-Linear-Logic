open import Data.List

module Utils.BigTensor (Atom : Set) where
  open import Logic.Core.Props Atom

  ⨂_ : List Prop → Prop
  ⨂ [] = 𝟙
  ⨂ (x ∷ xs) = x ⊗ (⨂ xs)
