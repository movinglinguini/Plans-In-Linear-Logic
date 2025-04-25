open import Data.Nat using (_+_; _∸_; ℕ)
open import Data.Fin hiding (_+_)
open import Data.List hiding (merge)
open import Data.Vec
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum renaming ([_,_] to case-⊎)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any using (there; here)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵛ_)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_)
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
  -- A well-formed problem minus a goal condition is still well-formed.
  ℙ⇒ℙ' : ∀ { g } (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 (g ∷ 𝔾))
    → PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾
  ℙ⇒ℙ' {𝔾 = 𝔾} (wf/prob 𝕋 ℂ 𝕀 𝕆 .(_ ∷ 𝔾) wf/conds wf/state (wf/state/s wf/goal x)) 
    = wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾 wf/conds wf/state wf/goal

  translg-∈-ctxt : ∀ { g } (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)
    → g ∈ˡ 𝕀
    → ⟨ translConfig-Condition g , Linear ⟩ ∈ᵛ (proj₂ (proj₁ (translProb ℙ)))
  translg-∈-ctxt ℙ mem = ∈-state-context⇒∈-context ℙ (∈-state⇒∈-state-context ℙ mem)

  correctness-base : ∀ { tℙ }
    → (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)
    → Sat 𝕀 𝔾
    → tℙ ≡ translProb ℙ
    → (exh-state : List (Fin (Data.List.length 𝕆 + Data.List.length 𝕀)))
    → irrelify-Vec (proj₁ tℙ) exh-state ⊢ⁱ (proj₂ tℙ)
  correctness-base (wf/prob _ _ _ _ [] wf/conds wf/state wf/goal) sat refl exh-state = {!  !}
  correctness-base (wf/prob _ _ _ _ (⟨ c , false ⟩ ∷ 𝔾) wf/conds wf/state wf/goal) sat refl exh-state = {!   !}
  correctness-base { tℙ = tℙ } (wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ c , true ⟩ ∷ 𝔾) wf/conds wf/state wf/goal) (sat/s sat mem) refl exh-state 
    = ⊗-assoc 
      (⊗R M12 M23 M {!   !} 
        (id (proj₂ (irrelify-allbut⇒update {!   !} refl)) {!   !}) 
        IH)
    where
      ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 (⟨ c , true ⟩ ∷ 𝔾)
      ℙ = wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ c , true ⟩ ∷ 𝔾) wf/conds wf/state wf/goal

      tg-∈-ctxt = translg-∈-ctxt ℙ mem
      tg-idx = ∈⇒idx (proj₁ tℙ) tg-∈-ctxt
      Itℙ = (irrelify-Vec (proj₁ tℙ) exh-state)

      Δ₁₂ = irrelify-AllBut (proj₁ tℙ) tg-idx
      Δ₂₃ = irrelify-Vec (proj₁ tℙ) (tg-idx ∷ exh-state)

      IH : Δ₂₃ ⊢ⁱ ⟨ (⨂ translConfig 𝔾) ⊗ ⊤ , Linear ⟩
      IH with ℙ⇒ℙ' ℙ
      ... | wf/prob .𝕋 .ℂ .𝕀 .𝕆 .𝔾 wf/conds wf/state wf/goal 
        = correctness-base (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾 wf/conds wf/state wf/goal) sat refl ((∈⇒idx (proj₁ tℙ) tg-∈-ctxt) ∷ exh-state) -- correctness-base { tℙ = (translProb ℙ') } ℙ' sat {!   !} {!   !}

      M12 : merge {!   !} {!   !} Δ₁₂
      M23 : merge {!   !} {!   !} Δ₂₃
      M : merge Δ₁₂ {!   !} Itℙ

      U = irrelify-allbut⇒update { Δ = (proj₁ tℙ) } { Δ' = Δ₂₃ } {!  !} {!   !} 

      -- U = irrelify-allbut⇒update { Δ' = Δ₁₂ } tg-∈-ctxt refl
      -- U-weak : cWeakenable (proj₁ U)
      -- U-weak = irrelify-allbut-update-irr-irr { Δ' = Δ₁₂ } refl

      -- IH : Δ₂₃ ⊢ⁱ ⟨ (⨂ translConfig 𝔾) ⊗ ⊤ , Linear ⟩
      -- IH with ℙ⇒ℙ' ℙ
      -- ... | wf/prob .𝕋 .ℂ .𝕀 .𝕆 .𝔾 wf/conds wf/state wf/goal 
      --     = correctness-base (wf/prob 𝕋 ℂ 𝕀 {! 𝕆 !} 𝔾 wf/conds wf/state wf/goal) sat refl ((∈⇒idx (proj₁ tℙ) tg-∈-ctxt) ∷ exh-state)
        -- = correctness-base (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾 wf/conds wf/state wf/goal) sat refl ((∈⇒idx (proj₁ tℙ) tg-∈-ctxt) ∷ exh-state)
    
    -- → {! (exh-state : Vec (Σ (Prop × Mode) (λ Aₘ → Aₘ ∈ᵛ ?)) (Data.List.length 𝕀))  !}
    
  -- correctness-base {tℙ = tℙ} (wf/prob _ _ _ _ [] wf/conds wf/state wf/goal) sat exh-states refl = {!   !}
  -- correctness-base {tℙ = tℙ} (wf/prob _ _ _ _ (⟨ c , false ⟩ ∷ 𝔾) wf/conds wf/state wf/goal) sat exh-states refl = {!   !}
  -- correctness-base {tℙ = tℙ} (wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ c , true ⟩ ∷ 𝔾) wf/conds wf/state wf/goal) (sat/s sat mem) exh-states refl 
  --   = {!   !}
  --   where
  --     ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 (⟨ c , true ⟩ ∷ 𝔾)
  --     ℙ = wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ c , true ⟩ ∷ 𝔾) wf/conds wf/state wf/goal
  --     ℙ' : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾
  --     ℙ' = ℙ⇒ℙ' ℙ 

  --     tg = translConfig-Condition ⟨ c , true ⟩
  --     tg-∈-ctxt = translg-∈-ctxt ℙ mem

  --     Δ₁₂ = irrelify-AllBut (proj₁ tℙ) ⟨ tg , Linear ⟩ tg-∈-ctxt
  --     Δ₂₃ = irrelify-Only (proj₁ tℙ) ⟨ tg , Linear ⟩ tg-∈-ctxt

  --     M12 : merge {!   !} {!   !} Δ₁₂
  --     M23 : merge {!   !} {!   !} Δ₂₃

  --     U = irrelify-allbut⇒update { Δ' = Δ₁₂ } refl
  --     U-weak : cWeakenable (proj₁ U)
  --     U-weak = (irrelify-allbut-update-irr-irr { Δ' = Δ₁₂ }) refl
      
  --     IH : Δ₂₃ ⊢ⁱ ⟨ (⨂ (translConfig 𝔾)) ⊗ ⊤ , Linear ⟩
  --     IH = correctness-base ℙ' sat {!   !}
  {-  
    Our main theorem. Given that we have a well-formed plan that solves a well-formed planning problem,
    there exists a translation of the planning problem into a provable sequent.
  -}
  correctness : ∀ { ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 }
    → Plan 𝕀 𝔾
    → Σ  (Context ((2 + Data.List.length 𝕋) + 0) ((Data.List.length 𝕆) + (Data.List.length 𝕀)) × (Prop × Mode))
         λ (tℙ) → (proj₁ tℙ) ⊢ⁱ (proj₂ tℙ) 
  correctness {ℙ = ℙ} (wf/plan/z _ _ x) = ⟨ (translProb ℙ) , correctness-base ℙ x refl [] ⟩
  correctness { ℙ = ℙ } (wf/plan/s _ out τ _ plan x) = ⟨ translProb ℙ , {!   !} ⟩             