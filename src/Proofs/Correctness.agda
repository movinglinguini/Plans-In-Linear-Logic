open import Data.Nat using (_+_; _∸_; ℕ)
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.Vec
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum renaming ([_,_] to case-⊎)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any using (there; here)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any

open import ADJ.Core renaming (Term to AdjointTerm)
open import STRIPS.Problem renaming (Term to STRIPSTerm) hiding (update)
open import Translations.Translations 
open import Utils.IrrelifyContext
open import Utils.BigTensor

open import Proofs.LogicalPreorder

module Proofs.Correctness where
  {-
    Lemmas
  -}

  correctness-base : ∀ { tℙ }
    (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)
    → sat 𝕀 𝔾
    → tℙ ≡ translProb ℙ
    → proj₁ tℙ ⊢ⁱ proj₂ tℙ
  correctness-base ℙ sat refl with translProb ℙ
  correctness-base {𝔾 = []} (wf/prob _ _ _ _ .[] wf/conds wf/state wf/goal) sat refl | ⟨ a , a₁ ⟩ = ⊗R {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}
  correctness-base {𝔾 = x ∷ 𝔾} { tℙ = tℙ } (wf/prob 𝕋 ℂ 𝕀 𝕆 .(x ∷ 𝔾) wf/conds wf/state wf/goal) sat refl | ⟨ a , a₁ ⟩ with translG-Goals (x ∷ 𝔾)
  ... | tg ∷ tG = ⊗-assoc (⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) {!   !})
    where
      Ψ = (proj₁ tℙ)
      Ψ-glin = irrelify-AllBut Ψ ⟨ tg , Linear ⟩ {!   !}
      
  {-  
    Our main theorem. Given that we have a well-formed plan that solves a well-formed planning problem,
    there exists a translation of the planning problem into a provable sequent.
  -}
  correctness : ∀ { ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 }
    → Plan 𝕀 𝔾
    → Σ  (Context ((2 + Data.List.length 𝕋) + 0) ((Data.List.length 𝕆) + (Data.List.length 𝕀)) × (Prop × Mode))
         λ (tℙ) → (proj₁ tℙ) ⊢ⁱ (proj₂ tℙ) 
  correctness {ℙ = ℙ} (wf/plan/z _ _ x) = ⟨ (translProb ℙ) , correctness-base ℙ x refl ⟩
  correctness (wf/plan/s _ out τ _ plan x) = ⟨ {!   !} , {!   !} ⟩        