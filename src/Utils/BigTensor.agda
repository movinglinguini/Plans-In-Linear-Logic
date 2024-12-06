module Utils.BigTensor (U : Set) (T : Set) where
  open import ADJ.Core U T 

  ⨂_ : List (Prop Linear) → Prop Linear
  ⨂ ∅ = 𝟙
  ⨂ (x , xs) = x ⊗ (⨂ xs)