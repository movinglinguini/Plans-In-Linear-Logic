open import Data.Nat using (_+_)
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
  {-
    Lemmas
  -}
  emptyPlan⇒proof : ∀ ( P : PlanProblem ) (Pᵗ : (CtxtP P) × Prop)
    → sat (PlanProblem.initialState P) ⟨ PlanProblem.goals P)
    → Pᵗ ≡ translProb P
    → proj₁ Pᵗ ⊢ⁱ ⟨ proj₂ Pᵗ , Linear ⟩
  
  {-
    Our main theorem
  -}
  correctness : ∀ ( P : PlanProblem ) { T : Plan }
    → Solves (PlanProblem.initialState P) T (PlanProblem.goals P)
    → Σ ((CtxtP P) × Prop)
        (λ tP → (proj₁ tP) ⊢ⁱ ⟨ (proj₂ tP) , Linear ⟩)
  
  correctness P (solves/z x) = ⟨ translProb P , emptyPlan⇒proof P (translProb P) {!   !} refl ⟩
  correctness P (solves/s sol x) = ⟨ (translProb P) , {!   !} ⟩