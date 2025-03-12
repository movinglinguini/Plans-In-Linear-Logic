open import Data.Product 

module Proofs.LogicalPreorder where
  open import ADJ.Core

  data _≼_ : ∀ { x y } → Context x y → Context x y → Set where
    preceq : ∀ { x y } { Δ₁ Δ₂ : Context x y }
      → (∀ { C } → Δ₂ ⊢ⁱ C → Δ₁ ⊢ⁱ C)
      → Δ₁ ≼ Δ₂

  preceq-reflexive : ∀ { x y } { Δ : Context x y } → Δ ≼ Δ
  preceq-reflexive {Δ = Δ} = preceq (λ x₁ → x₁)

  preceq-transitive : ∀ { x y } { Δ₁ Δ₂ Δ₃ : Context x y } → Δ₁ ≼ Δ₂ → Δ₂ ≼ Δ₃ → Δ₁ ≼ Δ₃
  preceq-transitive (preceq x₁) (preceq x₂) = preceq (λ x₃ → x₁ (x₂ x₃)) 