open import Data.Vec

module Utils.BigTensor (Atom : Set) where
  open import Logic.Core.Props Atom

  ⨂_ : ∀ { n } → Vec Prop n → Prop
  ⨂ [] = 𝟙
  ⨂ (x ∷ xs) = x ⊗ (⨂ xs)
