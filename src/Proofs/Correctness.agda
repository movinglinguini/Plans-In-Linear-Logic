open import Data.Nat using (_+_; _∸_; ℕ)
open import Data.Fin hiding (_+_)
open import Data.List hiding (merge; _++_)
open import Data.Vec hiding (length)
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

  {- 
    Lemma: If 
  -}
  correctness-base : ∀ { Γ Δ }
    → (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)
    → Sat 𝕀 𝔾
    → (exh-state : List (Fin (Data.List.length 𝕀)))
    → Γ ≡ contextify-operators ℙ
    → Δ ≡ contextify-state ℙ
    → (lin/irr : LinOrIrr Δ)
    → (Γ ++ᶜ (proj₁ (irrelify-List-lin/irr Δ exh-state lin/irr ))) ⊢ⁱ proj₂ (translProb ℙ)
    -- → Σ (Context 0 (Data.List.length 𝕀))
    --     (λ Δ' → ((Γ ++ᶜ Δ') ⊢ⁱ (proj₂ (translProb ℙ)) × Comparable Δ Δ' × LinOrIrr Δ'))
  correctness-base { Δ = Δ } (wf/prob 𝕋 ℂ 𝕀 𝕆 [] wf/conds wf/state wf/goal) sat exh-state refl refl 
    = {!   !}
    where
      ℙ = wf/prob 𝕋 ℂ 𝕀 𝕆 [] wf/conds wf/state wf/goal
      Δ' = irrelify-List-lin/irr Δ (exh-state) (lin-to-lin/irr (Δ-linear ℙ))
  correctness-base {Γ = Γ} {Δ} (wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ g , false ⟩ ∷ 𝔾) wf/conds wf/state wf/goal) sat exh-state refl refl 
    = {!   !}
    where
      ℙ = wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ g , false ⟩ ∷ 𝔾) wf/conds wf/state wf/goal
      Δ' = irrelify-List-lin/irr Δ (exh-state) (lin-to-lin/irr (Δ-linear ℙ))
  correctness-base {Γ = Γ} {Δ} (wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ g , true ⟩ ∷ 𝔾) wf/conds wf/state (wf/state/s wf/goal x)) (sat/s sat mem) exh-state refl refl lin/irr
    = ⊗-assoc (⊗R M12 M23 M Δ₂-contract {!   !} (IH))
    where 
      ℙ = wf/prob 𝕋 ℂ 𝕀 𝕆 (⟨ g , true ⟩ ∷ 𝔾) wf/conds wf/state (wf/state/s wf/goal x)
      ℙ' = ℙ⇒ℙ' ℙ

      -- The translation of the goal (tg) at the head is in the state context
      tg-mem : ⟨ translConfig-Condition ⟨ g , true ⟩ , Linear ⟩ ∈ᵛ (proj₂ Δ)
      tg-mem = ∈-state⇒∈-state-context ℙ mem

      -- Using the vector membership constructor, we produce an index 
      -- for tg in the state context.
      tg-idx : Fin (length 𝕀)
      tg-idx = ∈⇒idx Δ tg-mem

      Δ' = irrelify-List-lin/irr Δ (exh-state) lin/irr
      Δ'' = irrelify-List-lin/irr Δ (tg-idx ∷ exh-state) (lin-to-lin/irr (Δ-linear ℙ))
      
      -- First, our IH
      IH = correctness-base (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾 wf/conds wf/state wf/goal) sat (tg-idx ∷ exh-state) refl refl lin/irr

      -- Now, we set up splitting our contexts
      -- The context that goes to the left will only contain the
      -- operators and only tg.
      Δ₁₂ = Γ ++ᶜ (irrelify-AllBut Δ tg-idx)
      -- The context that goes to the right will only contain the
      -- operators and whatever has not been exhausted already.
      Δ₂₃ = Γ ++ᶜ proj₁ (irrelify-List-lin/irr Δ (tg-idx ∷ exh-state) lin/irr)

      Δ₁ = Δ₁₂ -- Δ₁ is basically everything going to the left
      Δ₂ = Γ ++ᶜ (irrelify-All Δ) -- Δ₂ isn't useful here, so we irrelify all the linear part.
      Δ₃ = Δ₂₃ -- Δ₃ is basically everything going to the right

      -- Lemma: Δ₂ is contractable
      Δ₂-contract : cContractable Δ₂
      Δ₂-contract = concat-cContr refl (Γ-contractable ℙ) (irrelify-contract Δ)

      -- Now we need to explain how we are splitting our context
      M12 : merge Δ₁ Δ₂ Δ₁₂
      M12 = concat-merge (cUnrestricted-merge-id (Γ-unrestricted ℙ)) (irrelify-lin-merge (Δ-linear ℙ))
      M23 : merge Δ₂ Δ₃ Δ₂₃
      M23 = concat-merge 
        (cUnrestricted-merge-id (Γ-unrestricted ℙ))
        (irrel-lin/irr-merge-id-left 
          (proj₁ (proj₂ (irrelify-List-lin/irr Δ (tg-idx ∷ exh-state) lin/irr))) 
          (irrelify-irr Δ) 
          (comparable-trans 
            (comparable-comm (proj₂ (proj₂ (proj₂ (irrelify-List-lin/irr Δ (tg-idx ∷ exh-state) lin/irr))))) 
            (irrelify-all-comp Δ)))
                  
      M : merge Δ₁₂ Δ₃ (Γ ++ᶜ (proj₁ (irrelify-List-lin/irr Δ (exh-state) lin/irr)))
      M = concat-merge
            (cUnrestricted-merge-id (Γ-unrestricted ℙ)) 
            (irrelify-allbut-list-merge tg-idx exh-state lin/irr)
      
      -- Now, we prove we can use id to eliminate the translated goal
      -- To do that, we show that we can indeed update the tg so that
      -- it is exhausted/irrelevant in Δ₁₂. After that, we need
      -- to show that the updated context is weakenable. 

      -- First, a quick detour: we show that the element from the state
      -- context that we can find using tg-mem is the same element
      -- that we can find using tg-idx.
      tg-mem≡tg-idx = ∈≡idx Δ tg-idx tg-mem refl

      -- Lemma: We can update tg in Δ
      updateable-lem = irrelify-allbut⇒update { Δ = Δ } tg-mem≡tg-idx refl 
      -- Lemma: With the previous lemma, we can update in Γ ++ Δ
      updateable-Δ₁₂ = concat-update-r { Δ₂ = Γ } (proj₂ updateable-lem)
      -- Lemma: The updated Γ ++ Δ is weakenable. It must be since it
      -- is now all irrelevant
      updated-Δ₁₂-weak-lem = irrelify-allbut-upd-irrel-weak { Δ = Δ } tg-mem≡tg-idx refl refl
      -- Finally, with the above lemma and concat-cWeak, we can show that our entire
      -- updated context is cWeak
      updated-Δ₁₂-weak = concat-cWeak refl (Γ-weakenable ℙ) updated-Δ₁₂-weak-lem
        
  {-  
    Our main theorem. Given that we have a well-formed plan that solves a well-formed planning problem,
    there exists a translation of the planning problem into a provable sequent.
  -}
  correctness : ∀ { ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 }
    → Plan 𝕀 𝔾
    → Σ  (Context ((2 + Data.List.length 𝕋) + 0) ((Data.List.length 𝕆) + (Data.List.length 𝕀)) × (Prop × Mode))
         λ (tℙ) → (proj₁ tℙ) ⊢ⁱ (proj₂ tℙ) 
  correctness {ℙ = ℙ} (wf/plan/z _ _ x) = ⟨ (translProb ℙ) , {!   !} ⟩
  correctness { ℙ = ℙ } (wf/plan/s _ out τ _ plan x) = ⟨ translProb ℙ , {!   !} ⟩                             