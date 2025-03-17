open import Data.Nat using (_+_; _∸_)
open import Data.Fin hiding (_+_)
open import Data.List hiding (merge ; length)
open import Data.Vec
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum renaming ([_,_] to case-⊎)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any using (there; here)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any

open import Proofs.LogicalPreorder

module Proofs.Correctness where
  open import STRIPS.Problem renaming (Term to STRIPSTerm) hiding (update)
  open import Translations.Translations 
  open import ADJ.Core renaming (Term to AdjointTerm)
  open import Utils.IrrelifyContext
  open import Utils.BigTensor
  {-
    Lemmas
  -}
  {-
    Helper function for one of our main lemmas.
    If we have goal satisfaction, then we can prove the translation of the goal.
  -}
  sat𝕀⟨𝔾⟩⇒proof-lemma : ∀ { gs } { 𝔾 : Goals ℂ gs } { 𝐆 : Vec Prop (Data.List.length gs) } 
    ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → 𝐆 ≡ (translG-Goals 𝔾)
    → satGoals 𝕀 𝔾
    → proj₁ (translProb ℙ) ⊢ⁱ ⟨ (⨂ 𝐆) ⊗ ⊤ , Linear ⟩
  sat𝕀⟨𝔾⟩⇒proof-lemma (wf/prob _ _ _ _ wf/goal/z) refl satgoal 
    = ⊗R {!   !} {!   !} {!   !} {!   !} (𝟙R {!   !}) ⊤R
  sat𝕀⟨𝔾⟩⇒proof-lemma (wf/prob _ _ _ _ (wf/goal/s 𝔾 wfcond)) refl satgoal = {!   !}

  {-
    Lemma: If we have goal satisfaction, then we can prove the translation of the goal. We use the lemma
    sat𝕀⟨𝔾⟩⇒proof-lemma to allow us to recurse on ⨂ (translG-Goals 𝔾) (a.k.a., the translation of the goal into a)
    linear logic proposition.
  -}
  sat𝕀⟨𝔾⟩⇒proof : ∀ ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → satGoals 𝕀 𝔾
    → (proj₁ (translProb ℙ)) ⊢ⁱ ⟨ (⨂ (translG-Goals 𝔾)) ⊗ ⊤ , Linear ⟩
  sat𝕀⟨𝔾⟩⇒proof {𝔾 = 𝔾} P satgoal = sat𝕀⟨𝔾⟩⇒proof-lemma P refl satgoal

  {- 
    Lemma: If we're taking a step in the plan, then we have a step in our proof. We use the notion of the
    logical preorder to get us there.
  -}
  -- plan-step⇒proof-step : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 𝕀' } ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 ) (τ : GroundOperator) { ℙ' : PlanProblem 𝕋 ℂ 𝕀' 𝕆 𝔾}
  --   → 𝕀 ⟶[ τ ] 𝕀'
  --   → (proj₁ (translProb ℙ)) ≼ (proj₁ (translProb ℙ'))
  -- plan-step⇒proof-step ℙ τ (transition x x₁) = preceq (λ x₂ → ∀L {!   !} {!   !} {!   !} {!   !})

  {-
    Our main theorem. Given that we have a well-formed plan (a.k.a., one that solves the)
    given planning problem, there exists a translation of the planning problem into a
    provable sequent.
  -}
  correctness : ∀ { P : Plan } 
    → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → WfPlan ℙ P
    → Σ (Context ((2 + length 𝕋) + 0) ((length 𝕆) + (length ℂ)) × Prop)
        (λ tP → (proj₁ tP) ⊢ⁱ ⟨ (proj₂ tP) , Linear ⟩)
  correctness P (wf/plan/z satgoal) = ⟨ translProb P , sat𝕀⟨𝔾⟩⇒proof P satgoal ⟩
  correctness P (wf/plan/s {τ = τ} plan x) = {! P  !}   