open import Data.Nat using (_+_; _∸_; ℕ)
open import Data.Fin hiding (_+_)
open import Data.List hiding (merge ; length; _++_)
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
  A-list⇒⨂A : ∀ { n }
    → (Δ : Vec Prop n) 
    → ⟨ [] , Data.Vec.map (λ x → ⟨ x , Linear ⟩) Δ ⟩ ⊢ⁱ ⟨ (⨂ Δ) , Linear ⟩
  A-list⇒⨂A [] = 𝟙R weak/n
  A-list⇒⨂A (A ∷ Δ)  = ⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) {!  !}

  satG⇒proof-lemma' : ∀ { gs Δ } { 𝔾 : Goals gs ℂ } (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)
    → { delt : Δ ≡ proj₁ (translProb ℙ) }
    → Σ (ℕ) (λ q → Σ (Vec (Σ (Prop × Mode) (λ A → A ∈ proj₂ Δ)) q) (λ v → irrelify Δ v ⊢ⁱ ⟨ ⨂ (translConfig gs) , Linear ⟩ ))
  satG⇒proof-lemma' {gs = []} {Δ} (wf/prob _ _ _ _ wf/goal/z wf/conds wf/state) = ⟨ {!   !} , ⟨ {!   !} , 𝟙R {!   !} ⟩ ⟩
  satG⇒proof-lemma' {gs = ⟨ c , false ⟩ ∷ gs} (wf/prob 𝕋 ℂ 𝕀 𝕆 (wf/goal/s 𝔾 wfcond) wf/conds wf/state) = ⟨ {!   !} , ⟨ {!   !} , (⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) (proj₂ (proj₂ IH))) ⟩ ⟩
    where
      ℙ' = wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾 wf/conds wf/state
      IH = satG⇒proof-lemma' ℙ' { delt = refl }
  satG⇒proof-lemma' {gs = ⟨ c , true ⟩ ∷ gs} (wf/prob _ _ _ _ (wf/goal/s 𝔾 wfcond) wf/conds wf/state) = {!   !}

  satG⇒proof-lemma : ∀ gs (Γ : Context n m)
    → cWeakenable Γ
    → State 𝕀 ℂ
    → sat 𝕀 gs
    → Σ (Context (n + 0) (m + (length ℂ))) (λ Δ → Δ ⊢ⁱ ⟨ (⨂ (translConfig gs)) , Linear ⟩)


  -- If the state 
  satG⇒proof : ∀ { 𝔾 : Goals gs ℂ } (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)
    → sat 𝕀 gs
    → (proj₁ (translProb ℙ)) ⊢ⁱ (proj₂ (translProb ℙ))
  satG⇒proof ℙ sat = {!   !}
  
  {-  
    Our main theorem. Given that we have a well-formed plan that solves a well-formed planning problem,
    there exists a translation of the planning problem into a provable sequent.
  -}
  correctness : ∀ { ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 } { P : Plan (initialState ℙ) 𝔾 }
    → Solves ℙ P
    → Σ  (Context ((2 + length 𝕋) + 0) ((length 𝕆) + (length ℂ)) × (Prop × Mode))
         λ (tℙ) → (proj₁ tℙ) ⊢ⁱ (proj₂ tℙ) 
  correctness (solves ℙ (wf/plan/z .(initialState ℙ) _ x)) = ⟨ (translProb ℙ) , satG⇒proof ℙ x ⟩
  correctness (solves ℙ (wf/plan/s .(initialState ℙ) out τ trans P x)) = {!   !}         