open import Data.Vec

module Utils.BigTensor where
  open import Translations.Core.State
  open import Logic.Core.Props PropAtom

  ⨂_ : ∀ { n } → Vec Prop n → Prop
  ⨂ [] = 𝟙
  ⨂ (x ∷ xs) = x ⊗ (⨂ xs)
