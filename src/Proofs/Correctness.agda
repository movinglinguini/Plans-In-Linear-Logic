open import Data.Nat using (_+_; _∸_)
open import Data.Fin hiding (_+_)
open import Data.List hiding (merge)
open import Data.Vec hiding (length)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any
open import Data.Vec.Membership.Propositional

module Proofs.Correctness where
  open import STRIPS.Problem renaming (Term to STRIPSTerm) hiding (update)
  open import Translations.Translations 
  open import ADJ.Core renaming (Term to AdjointTerm)
  open import Utils.IrrelifyContext
  open import Utils.BigTensor
  {-
    Lemmas
  -- -}
  -- emptyPlan⇒proof : ∀ ( P : PlanProblem ) (Pᵗ : (CtxtP P) × Prop)
  --   → Solves (PlanProblem.initialState P) [] (PlanProblem.goals P)
  --   → Pᵗ ≡ translProb P
  --   → proj₁ Pᵗ ⊢ⁱ ⟨ proj₂ Pᵗ , Linear ⟩
  -- emptyPlan⇒proof P Pᵗ (solves/z ⟨ fst , snd ⟩) refl with PlanProblem.goals P | translG P
  -- ... | record { pos = [] ; neg = [] } | [] = ⊗R M12 M23 M Δ'-cContr (𝟙R Δ'-cWeak) ⊤R
  --   where
  --     Δₛ = contextify-state P
  --     Δₒ = contextify-operators P
  --     IΔₛ = makeAllIrrel Δₛ
      
  --     Δ = Δₒ ++ᶜ Δₛ
  --     Δ' = Δₒ ++ᶜ IΔₛ

  --     M12-lemma-1 : merge Δₒ Δₒ Δₒ
  --     M12-lemma-1 = context-operator-merge { P = P } refl

  --     M12-lemma-2 : merge IΔₛ IΔₛ IΔₛ
  --     M12-lemma-2 = irrelify-merge-i refl

  --     M12 : merge Δ' Δ' Δ'
  --     M12 = concat-merge M12-lemma-1 M12-lemma-2

  --     M23-lemma-1 = M12-lemma-1

  --     M23-lemma-2 : merge IΔₛ Δₛ Δₛ
  --     M23-lemma-2 = irrelify-merge-l refl (context-state-all-lin { P = P })

  --     M23 : merge Δ' Δ Δ
  --     M23 = concat-merge M23-lemma-1 M23-lemma-2 

  --     M = M23

  --     Δ'-cContr-lemma-1 : cContractable Δₒ
  --     Δ'-cContr-lemma-1 = context-operator-cContr { P = P }

  --     Δ'-cContr-lemma-2 : cContractable IΔₛ 
  --     Δ'-cContr-lemma-2 = irrelify-is-cContr refl

  --     Δ'-cContr : cContractable Δ'
  --     Δ'-cContr = concat-cContr refl Δ'-cContr-lemma-1 Δ'-cContr-lemma-2

  --     Δ'-cWeak-lemma-1 : cWeakenable Δₒ
  --     Δ'-cWeak-lemma-1 = context-operator-cWeak { P = P }

  --     Δ'-cWeak-lemma-2 : cWeakenable IΔₛ
  --     Δ'-cWeak-lemma-2 = irrelify-is-cWeak refl

  --     Δ'-cWeak : cWeakenable Δ'
  --     Δ'-cWeak = concat-cWeak refl Δ'-cWeak-lemma-1 Δ'-cWeak-lemma-2 


  -- ... | record { pos = [] ; neg = x ∷ neg } | x₁ ∷ b = {!   !}
  -- ... | record { pos = x ∷ pos ; neg = [] } | x₁ ∷ b = {!   !}
  -- ... | record { pos = x ∷ pos ; neg = x₁ ∷ neg } | x₂ ∷ b = {!   !}

  sat𝕀⟨𝔾⟩⇒proof-lemma : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 ) 
    → ( 𝐆 : Vec Prop (Data.List.length 𝔾) )
    → satGoal 𝕀 𝔾
    → 𝐆 ≡ translG ℙ
    → (proj₁ (translProb ℙ)) ⊢ⁱ ⟨ ⨂ 𝐆 , Linear ⟩
  sat𝕀⟨𝔾⟩⇒proof-lemma {𝔾 = []} (wf/prob _ _ _ _ .[] x x₁ x₂ x₃) .(translG (wf/prob _ _ _ _ [] x x₁ x₂ x₃)) satgoal refl = 𝟙R {!   !}
  sat𝕀⟨𝔾⟩⇒proof-lemma {𝔾 = x ∷ 𝔾} (wf/prob _ _ _ _ .(x ∷ 𝔾) x₁ x₂ x₃ x₄) .(translG (wf/prob _ _ _ _ (x ∷ 𝔾) x₁ x₂ x₃ x₄)) satgoal refl with translG-Goals (x ∷ 𝔾)
  ... | g ∷ gs = ⊗R {!   !} {!   !} {!   !} {!   !} {!   !} (sat𝕀⟨𝔾⟩⇒proof-lemma (wf/prob {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}) gs {!   !} {!   !})

  sat𝕀⟨𝔾⟩⇒proof : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → satGoal 𝕀 𝔾
    → (proj₁ (translProb ℙ)) ⊢ⁱ ⟨ (proj₂ (translProb ℙ)) , Linear ⟩
  sat𝕀⟨𝔾⟩⇒proof P satgoal = ⊗R {!   !} {!   !} {!   !} {!   !} (sat𝕀⟨𝔾⟩⇒proof-lemma P (translG P) satgoal refl) ⊤R

  {-
    Our main theorem
  -}
  correctness : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → { P : Plan } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → WfPlan ℙ P
    → Σ (Context ((2 + length 𝕋) + 0) ((length 𝕆) + (length ℂ)) × Prop)
        (λ tP → (proj₁ tP) ⊢ⁱ ⟨ (proj₂ tP) , Linear ⟩)
  correctness P (wf/plan/z satgoal) = ⟨ translProb P , sat𝕀⟨𝔾⟩⇒proof P satgoal ⟩
  correctness .(wf/prob _ _ _ _ _ _ _ _ _) (wf/plan/s wfupdate satτ wfplan x) = {!   !}
  -- correctness : ∀ ( P : PlanProblem ) { T : Plan }
  --   → Solves (PlanProblem.initialState P) T (PlanProblem.goals P)
  --   → Σ ((CtxtP P) × Prop)
  --       (λ tP → (proj₁ tP) ⊢ⁱ ⟨ (proj₂ tP) , Linear ⟩)
  
  -- correctness P (solves/z x) = ⟨ translProb P , emptyPlan⇒proof P (translProb P) (solves/z x) refl ⟩
  -- correctness P (solves/s sol x) = ⟨ (translProb P) , {!   !} ⟩      