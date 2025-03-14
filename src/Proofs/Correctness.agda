open import Data.Nat using (_+_; _∸_)
open import Data.Fin hiding (_+_)
open import Data.List hiding (merge)
open import Data.Vec hiding (length)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any using (there; here)
open import Data.Vec.Membership.Propositional

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
  sat𝕀⟨𝕘∷𝔾⟩⇒g∈I : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 𝕘 } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → sat-Conditions 𝕀 (𝕘 ∷ 𝔾)
    → ⟨ translG-Goal 𝕘 , Linear ⟩ ∈ translS-Conditions 𝕀 ℂ
  sat𝕀⟨𝕘∷𝔾⟩⇒g∈I {𝕘 = ⟨ c , false ⟩} (wf/prob _ _ _ _ _ (wf/goal x)) sat = {!   !}
  sat𝕀⟨𝕘∷𝔾⟩⇒g∈I {𝕘 = ⟨ c , true ⟩} (wf/prob _ _ _ _ _ (wf/goal x)) sat = {!   !}

  {-
    Helper function for one of our main lemmas.
    If we have goal satisfaction, then we can prove the translation of the goal.
  -}
  sat𝕀⟨𝔾⟩⇒proof-lemma : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 ) { gs : Vec Prop (length 𝔾) }
    → gs ≡ (translG-Goals 𝔾)
    → sat-Conditions 𝕀 𝔾
    → proj₁ (translProb ℙ) ⊢ⁱ ⟨ (⨂ gs) ⊗ ⊤ , Linear ⟩
  sat𝕀⟨𝔾⟩⇒proof-lemma {𝔾 = []} P refl satgoal = {!   !}
  sat𝕀⟨𝔾⟩⇒proof-lemma {𝔾 = ⟨ c , false ⟩ ∷ 𝔾} P {g ∷ gs} _ satgoal = {!   !}
  sat𝕀⟨𝔾⟩⇒proof-lemma {𝔾 = ⟨ c , true ⟩ ∷ 𝔾} P {g ∷ gs} _ satgoal = {!   !}
  -- sat𝕀⟨𝔾⟩⇒proof-lemma {𝔾 = ⟨ c , false ⟩ ∷ 𝔾} (wf/prob 𝕋 ℂ 𝕀 𝕆 .(⟨ c , false ⟩ ∷ 𝔾)) {.(translG-Goal c false) ∷ .(translG-Goals 𝔾)} refl satgoal = ?
    -- = ⊗-assoc (⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) IH)
    -- where
    --   ℙ' = wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾

    --   g : Prop × Mode
    --   g = ⟨ translG-Goal c false , Linear ⟩

    --   IH : proj₁ (translProb ℙ') ⊢ⁱ ⟨ (⨂ translG-Goals 𝔾) ⊗ ⊤ , Linear ⟩
    --   IH = sat𝕀⟨𝔾⟩⇒proof-lemma ℙ' refl (satg∷G⇒satG satgoal)

    --   Δₛ = contextify-state ℙ'
    --   Δₒ = contextify-operators ℙ'

    --   Δ = Δₒ ++ᶜ Δₛ
    --   Δ₁ = Δₒ ++ᶜ (makeAllIrrelExcept g Δₛ {!   !})

      -- Δ₁ = Δₒ ++ᶜ (makeAllIrrelExcept Δₛ

    -- = ⊗-assoc (⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) (sat𝕀⟨𝔾⟩⇒proof-lemma (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾) (translGg∷gs⇒translGgs {!   !}) (satg∷G⇒satG satgoal)))
  -- sat𝕀⟨𝔾⟩⇒proof-lemma {𝔾 = ⟨ fst , true ⟩ ∷ 𝔾} (wf/prob 𝕋 ℂ 𝕀 𝕆 .(⟨ fst , true ⟩ ∷ 𝔾)) r satgoal = {!   !}
    -- = ⊗-assoc (⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) IH) 
    -- where
    --   ℙ' = wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾
    --   gs = translG-Goals 𝔾

    --   IH : proj₁ (translProb ℙ') ⊢ⁱ ⟨ (⨂ gs) ⊗ ⊤ , Linear ⟩
    --   IH = sat𝕀⟨𝔾⟩⇒proof-lemma ℙ' refl (satg∷G⇒satG satgoal)

    --   g = ⟨ translG-Goal (proj₁ x) (proj₂ x) , Linear ⟩

    --   Δₛ = contextify-state ℙ'
    --   Δₒ = contextify-operators ℙ'

    --   g∈Δₛ : g ∈ proj₂ Δₛ
    --   g∈Δₛ = {!   !}

    --   IΔₛ = makeAllIrrelExcept g Δₛ {!   !}

      -- Δ₁₂ 

  {-
    Lemma: If we have goal satisfaction, then we can prove the translation of the goal. We use the lemma
    sat𝕀⟨𝔾⟩⇒proof-lemma to allow us to recurse on ⨂ (translG-Goals 𝔾) (a.k.a., the translation of the goal into a)
    linear logic proposition.
  -}
  sat𝕀⟨𝔾⟩⇒proof : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → sat-Conditions 𝕀 𝔾
    → (proj₁ (translProb ℙ)) ⊢ⁱ ⟨ (⨂ (translG-Goals 𝔾)) ⊗ ⊤ , Linear ⟩
  sat𝕀⟨𝔾⟩⇒proof {𝔾 = 𝔾} P satgoal = sat𝕀⟨𝔾⟩⇒proof-lemma P refl satgoal

  {- 
    Lemma: If we're taking a step in the plan, then we have a step in our proof. We use the notion of the
    logical preorder to get us there.
  -}
  plan-step⇒proof-step : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 𝕀' } ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 ) (τ : GroundOperator) { ℙ' : PlanProblem 𝕋 ℂ 𝕀' 𝕆 𝔾}
    → 𝕀 ⟶[ τ ] 𝕀'
    → (proj₁ (translProb ℙ)) ≼ (proj₁ (translProb ℙ'))
  plan-step⇒proof-step ℙ τ (transition x x₁) = preceq (λ x₂ → ∀L {!   !} {!   !} {!   !} {!   !})

  {-
    Our main theorem. Given that we have a well-formed plan (a.k.a., one that solves the)
    given planning problem, there exists a translation of the planning problem into a
    provable sequent.
  -}
  correctness : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → { P : Plan } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → WfPlan ℙ P
    → Σ (Context ((2 + length 𝕋) + 0) ((length 𝕆) + (length ℂ)) × Prop)
        (λ tP → (proj₁ tP) ⊢ⁱ ⟨ (proj₂ tP) , Linear ⟩)
  correctness P (wf/plan/z satgoal) = ⟨ translProb P , sat𝕀⟨𝔾⟩⇒proof P satgoal ⟩
  correctness P (wf/plan/s {τ = τ} plan x) = {! P  !} 