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
  
  {-# TERMINATING #-}
  sat𝕀⟨𝔾⟩⇒proof : ∀ ( P : PlanProblem )
    → sat (PlanProblem.initialState P) (⟨ Goal.pos (PlanProblem.goals P) , Goal.neg (PlanProblem.goals P) ⟩)
    → translProb P
  sat𝕀⟨𝔾⟩⇒proof record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = [] ; neg = [] } } sat 
    = ⊗R M12 M23 M23 Δ12-cContr (𝟙R Δ12-cWeak) ⊤R
      where
        P = record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = [] ; neg = [] } }
        Δₛ = contextify-state P
        Δₒ = contextify-operators P
        IΔ = makeAllIrrel Δₛ
        Δ12 = Δₒ ++ᶜ IΔ
        
        IΔ-cWeak : cWeakenable IΔ
        IΔ-cWeak = irrelify-is-cWeak { Δ = Δₛ } refl

        Δₒ-cWeak : cWeakenable Δₒ
        Δₒ-cWeak = context-operator-cWeak { P = P }  

        Δ12-cWeak : cWeakenable Δ12
        Δ12-cWeak = concat-cWeak { Δ₁ = Δₒ } { Δ₂ = IΔ } refl Δₒ-cWeak IΔ-cWeak

        Δ12-cContr : cContractable Δ12
        Δ12-cContr = concat-cContr { Δ₁ = Δₒ } { Δ₂ = IΔ } refl (context-operator-cContr { P = P }) (irrelify-is-cContr { Δ = Δₛ } refl)

        M12 : merge Δ12 Δ12 Δ12
        M12 = concat-merge { Δ₄ = IΔ } (context-operator-merge { P = P } refl) (irrelify-merge-i { Δ = Δₛ } refl)

        M23 : merge Δ12 (Δₒ ++ᶜ Δₛ) (Δₒ ++ᶜ Δₛ)
        M23 = concat-merge { Δ₁ = Δₒ } { Δ₄ = IΔ } { Δ₅ = Δₛ } { Δ₆ = Δₛ } (context-operator-merge { P } refl) (irrelify-merge-l refl (context-state-all-lin { P }))
  
  sat𝕀⟨𝔾⟩⇒proof record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = [] ; neg = (x ∷ neg) } } sats 
    = ⊗-assoc (⊗R M12 M23 M Δ12'-cContr (id 𝕘-usable Δ12'-cWeak) (sat𝕀⟨𝔾⟩⇒proof P' sat'))
      where
        -- For the IH, we need proof that the initial state of P still satisfies the goal even after we've removed a condition of the goal
        P = record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = [] ; neg = (x ∷ neg) } }
        P' = record { PlanProblem P ; goals = record { pos = [] ; neg = neg } }
        
        sat' : sat (PlanProblem.initialState P') ⟨ [] , neg ⟩ 
        sat' = ⟨ (λ p x₁ → proj₁ sats p x₁), (λ p x₁ x₂ → proj₂ sats p (there x₁) x₂) ⟩
        
        𝕘 : Prop
        𝕘 = ` v[ translC x , term "false" ]

        Δₛ = contextify-state P'
        Δₒ = contextify-operators P'

        gInState : ⟨ 𝕘 , Linear ⟩ ∈ (proj₂ Δₛ)
        gInState = {!   !}

        IΔ-mostly = makeAllIrrelExcept ⟨ 𝕘 , Linear ⟩ Δₛ gInState  
        IΔ-total = makeAllIrrel Δₛ
        IΔ-one = onlyIrrelify ⟨ 𝕘 , Linear ⟩ Δₛ gInState
        
        Δ12 = Δₒ ++ᶜ IΔ-mostly
        Δ12' = Δₒ ++ᶜ IΔ-total

        Δ12'-cWeak : cWeakenable Δ12'
        Δ12'-cWeak = concat-cWeak { Δ₁ = Δₒ } { Δ₂ = IΔ-total } refl (context-operator-cWeak { P = P' }) (irrelify-is-cWeak refl)
        
        Δ12'-cContr : cContractable Δ12'
        Δ12'-cContr = concat-cContr { Δ₁ = Δₒ } { Δ₂ = IΔ-total } refl (context-operator-cContr { P = P' }) (irrelify-is-cContr refl) 

        Δ1 = Δ12
        Δ2 = Δ12'
        Δ3 = Δₒ ++ᶜ IΔ-one
        
        𝕘-usable : update Δ12 ⟨ 𝕘 , Linear ⟩ ⟨ 𝕘 , Irrelevant ⟩ Δ12'
        𝕘-usable = {!   !}

        M12-lemma : merge IΔ-mostly IΔ-total IΔ-mostly
        M12-lemma = {!   !}

        M12 : merge Δ1 Δ2 Δ12
        M12 = concat-merge (context-operator-merge { P' } refl) M12-lemma

        M23-lemma : merge IΔ-total IΔ-one Δₛ
        M23-lemma = {!   !}
        
        M23 : merge Δ2 Δ3 (contextOfProblem P')
        M23 = concat-merge (context-operator-merge { P' } refl) M23-lemma

        M : merge Δ12 Δ3 (contextOfProblem P')
        M = {!   !}


  sat𝕀⟨𝔾⟩⇒proof record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = (x ∷ pos) ; neg = [] } } sat = {!   !}
  
  sat𝕀⟨𝔾⟩⇒proof record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = (x ∷ pos) ; neg = (x₁ ∷ neg) } } sat = {!   !}
    
  correctness : ∀ { P : PlanProblem } { Τ : Plan }
    → Solves (PlanProblem.initialState P) Τ (PlanProblem.goals P)
    → Σ (Context × Prop) (λ ⟨ Γ , 𝔾 ⟩ → ⟨ Γ , 𝔾 ⟩ ≡ translProb P × Γ ⊢ⁱ 𝔾)

  correctness { P = P } (solves/z x) = sat𝕀⟨𝔾⟩⇒proof P x
  correctness (solves/s sol x) = {!   !}
     