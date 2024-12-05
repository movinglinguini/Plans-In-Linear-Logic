module Utils.BigTensor (a : Set) where
  open import ADJ.Core a

  ⨂_ : List a → Prop L
  ⨂ ∅ = 𝟙
  ⨂ (x , xs) = (` x) ⊗ (⨂ xs)