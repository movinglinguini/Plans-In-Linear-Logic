open import Data.List

open import Plans.Domain

module Utils.BigTensor (domain : Domain) where
  open Domain domain
  open import ADJ.Core domain

  ⨂_ : List (Prop) → Prop
  ⨂ [] = 𝟙
  ⨂ (x ∷ xs) = x ⊗ (⨂ xs)