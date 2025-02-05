open import Data.List using (List; _∷_; []; map)
open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Plans.Domain
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)

module Proofs.Correctness (domain : Domain) where
  -- Planning
  open Domain domain
  open import Plans.Plan domain
  open import Plans.Semantics domain
  
  -- Syntax
  open import Syntax.Core domain

  -- Translations
  open import Translations.Problem domain
  open import Translations.State domain
  open import Translations.Goal domain
  open import Translations.Operator domain

  -- ADJ
  open import ADJ.Core domain renaming (Context to AdjContext)

  open import Utils.BigTensor domain
  open import Utils.PlanToList domain
  open import Utils.WorldState domain

  variable
    ℙ : Plan

  {--
    Helper functions
  --}
  makeAllIrrelevant : AdjContext y n → AdjContext y n
  makeAllIrrelevant ⟨ fst , snd ⟩ = ⟨ fst , (Data.Vec.map (λ (⟨ p , m ⟩) → ⟨ p , Irrelevant ⟩) (snd)) ⟩

  data AllIrrelevant : AdjContext y n → AdjContext y n → Set where
    Z : AllIrrelevant ⟨ 𝕋 , [] ⟩ ⟨ 𝕋 , [] ⟩

    S : AllIrrelevant Δ₁ Δ₂
      -------------------------------
      → AllIrrelevant ⟨ proj₁ Δ₁ , ⟨ A , m ⟩ ∷ proj₂ Δ₁ ⟩ ⟨ proj₁ Δ₂ , ⟨ A , Irrelevant ⟩ ∷ proj₂ Δ₂ ⟩

  data AllLinear : AdjContext y n → Set where
    Z : AllLinear ⟨ 𝕋 , [] ⟩
    S : AllLinear ⟨ proj₁ Δ , proj₂ Δ ⟩
      -----------------------
      → AllLinear ⟨ proj₁ Δ , ⟨ A , Linear ⟩ ∷ proj₂ Δ ⟩
  
  data AllUnrestricted : AdjContext y n → Set where 
    Z : AllUnrestricted ⟨ 𝕋 , [] ⟩
    S : AllUnrestricted ⟨ proj₁ Δ , proj₂ Δ ⟩
      -----------------------
      → AllUnrestricted ⟨ proj₁ Δ , ⟨ A , Unrestricted ⟩ ∷ proj₂ Δ ⟩

  isIrrel : Δ₂ ≡ (makeAllIrrelevant Δ₁) → AllIrrelevant Δ₁ Δ₂
  isIrrel {Δ₁ = ⟨ fst , [] ⟩} refl = Z
  isIrrel {Δ₁ = ⟨ fst , x ∷ snd ⟩} refl = S (isIrrel refl)
  
  irrelWeak : AllIrrelevant Δ₁ Δ₂ → cWeakenable Δ₂
  irrelWeak Z = cWeakenable.weak/n
  irrelWeak (S irrel) = cWeakenable.weak/c (irrelWeak irrel) mweak/i

  irrelContr : AllIrrelevant Δ₁ Δ₂ → cContractable Δ₂
  irrelContr Z = cContractable.cont/n
  irrelContr (S irrel) = cContractable.cont/c (irrelContr irrel) mcontract/i

  irrelMerge : AllIrrelevant Δ₁ Δ₂ → AllLinear Δ₁ → merge Δ₂ Δ₁ Δ₁
  irrelMerge Z linear = merge.mg/n
  irrelMerge (S {m = Linear} irrel) (S linear) = merge.mg/c (irrelMerge irrel linear) i∙l

  SContextIsLinear : TranslS 𝕊 𝕊ᵗ → SContext 𝕊ᵗ Δ → AllLinear Δ
  SContextIsLinear {[]} wfS Z = Z
  SContextIsLinear {x ∷ 𝕊} (S {𝕊ᵗ = 𝕊ᵗ} wfS) (S {Δ = ⟨ [] , snd ⟩} wfΔ) = S (SContextIsLinear wfS wfΔ)

  {---------
    Lemmas
  ----------}
  satS-to-proveS : ∀ (𝕎 : World ) ( Δ₁ : AdjContext y n)
    → 𝕀 ∈⟨ 𝔾 ⟩ 
    → 𝕊 ≡ worldToState 𝕀 𝕎
    → TranslG 𝔾 𝔾ᵗ 
    → TranslS 𝕊 𝕊ᵗ
    → SContext 𝕊ᵗ Δ₂
    → Concat Δ₁ Δ₂ Δ
    → Δ ⊢ⁱ ⟨ 𝔾ᵗ ⊗ ⊤ , Linear ⟩

  satS-to-proveS {𝔾 = 𝔾} {𝔾ᵗ = 𝕘ᵗ ⊗ 𝔾ᵗ} {Δ = Δ} �� Δ₁ satG WtS (S wfG) wfS wfΔ₂ wfΔ = ⊗-assoc (⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) (satS-to-proveS �� Δ₁ ⟨ (λ a x → satG .proj₁ a (there x)) , (λ a z → satG .proj₂ a (there z)) ⟩ WtS wfG wfS wfΔ₂ wfΔ))
  satS-to-proveS {𝔾 = 𝔾} {𝔾ᵗ = 𝟙} {Δ = ⟨ fst , snd ⟩} �� Δ₁ satG WtS wfG wfS wfΔ₁ wfΔ = {!   !}
  -- satS-to-proveS {𝔾 = 𝔾} {𝔾ᵗ = 𝕘ᵗ ⊗ �ᵗ} 𝕎 Δ₂ satG WtS (S wfG) wfS wfΔ = ? -- ⊗-assoc (⊗R {!   !} {!   !} {!   !} {!   !} {!   !} (satS-to-proveS 𝕎 ⟨ (λ a z → satG .proj₁ a (there z)) , (λ a z → satG .proj₂ a (there z)) ⟩ WtS wfG wfS wfΔ))
  -- satS-to-proveS {𝔾 = 𝔾} {[]} {𝔾ᵗ = 𝟙} {Δ = ⟨ fst , [] ⟩} 𝕎 Δ₂ satG WtS Z wfS wfΔ = ⊗R M12 M23 M cContractable.cont/n (𝟙R cWeakenable.weak/n) ⊤R
  --   where
  --     ΔI = makeAllIrrelevant ⟨ fst , [] ⟩
  --     M12 : merge ΔI ΔI ΔI
  --     M12 = merge.mg/n
  --     M23 : merge ΔI ⟨ fst , [] ⟩ ⟨ fst , [] ⟩
  --     M23 = merge.mg/n
  --     M : merge ΔI ⟨ fst , [] ⟩ ⟨ fst , [] ⟩
  --     M = merge.mg/n
  -- satS-to-proveS {𝔾 = 𝔾} {x ∷ 𝕊} {𝔾ᵗ = 𝟙} {Δ = ⟨ fst , x₁ ∷ snd ⟩} 𝕎 satG WtS Z wfS wfΔ = ⊗R M12 M23 M ΔIcont (𝟙R ΔIweak) ⊤R
  --   where
  --     ΔI = makeAllIrrelevant ⟨ fst , x₁ ∷ snd ⟩
  --     ΔIisIrrel : AllIrrelevant ⟨ fst , x₁ ∷ snd ⟩ ΔI
  --     ΔIisIrrel = isIrrel refl

  --     ΔisLinear : AllLinear ⟨ fst , x₁ ∷ snd ⟩
  --     ΔisLinear = SContextIsLinear wfS wfΔ
                  
  --     M12 : merge ΔI ΔI ΔI
  --     M12 = irrelMerge {! ΔIisIrrel  !} {!   !}
  --     M23 : merge ΔI ⟨ fst , x₁ ∷ snd ⟩ ⟨ fst , x₁ ∷ snd ⟩
  --     M : merge ΔI ⟨ fst , x₁ ∷ snd ⟩ ⟨ fst , x₁ ∷ snd ⟩
  --     M = {!   !}

  --     ΔIweak : cWeakenable ΔI
  --     ΔIweak = irrelWeak ΔIisIrrel

  --     ΔIcont : cContractable ΔI
  --     ΔIcont = irrelContr ΔIisIrrel
  {--
    Correctness Theorem
  --}
  correctness : ∀ (𝕎 : World)
    → Γ ⊢ ℙ ∶ 𝕀 ↝ 𝔾
    → 𝕊 ≡ worldToState 𝕀 𝕎
    → TranslG 𝔾 𝔾ᵗ
    → TranslOs (Data.List.map Γ (planToList ℙ)) 𝕆ᵗ
    → TranslS 𝕊 𝕀ᵗ
    → OContext 𝕆ᵗ Δ₁
    → SContext 𝕀ᵗ Δ₂ 
    → Concat Δ₁ Δ₂ Δ
    → Δ ⊢ⁱ ⟨ 𝔾ᵗ ⊗ ⊤ , Linear ⟩ 
  
  correctness {Δ₁ = Δ₁} 𝕎 (halt IsatG) state wfG wfO wfS wfΔ₁ wfΔ₂ wfΔ = satS-to-proveS 𝕎 Δ₁ IsatG state wfG wfS wfΔ₂ wfΔ
  correctness 𝕎 (seq x plan) state wfG wfO wfS wfΔ₁ wfΔ₂ wfΔ = {!   !}    