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
  open import Utils.BigTensor Proposition
  open import Utils.IrrelifyContext

  -- sat𝕀⟨𝔾⟩⇒proof : ∀ { n m } → { Δ : Context n m } 
  --   → TranslTs 𝕋 𝕋ᵗ
  --   → TranslS 𝕀 ℙ 𝕀ᵗ
  --   → TranslG 𝔾 𝔾ᵗ
  --   → sat 𝕀 ⟨ Goal.pos 𝔾 , Goal.neg 𝔾 ⟩
  --   → Δ ⊢ⁱ 𝔾ᵗ

  -- sat𝕀⟨𝔾⟩⇒proof {n = n} {m = m} {Δ = ⟨ fst , [] ⟩} tT tS translG/z sat = {!   !}
  --   where
  --     IΔ : Context n m
  --     IΔ = makeAllIrrel ⟨ fst , [] ⟩

  --     isIrrel : Irrelified ⟨ fst , [] ⟩ IΔ
  --     isIrrel = irrelify/z

  --     contractableIΔ : cContractable IΔ
  --     contractableIΔ = cont/n

  --     M12 : merge IΔ IΔ IΔ
  --     M12 = mg/n
  --     M23 : merge IΔ Δ Δ
  --     M23 = {!   !}
  --     M : merge IΔ Δ Δ

  -- sat𝕀⟨𝔾⟩⇒proof {n = n} {m = m} {Δ = ⟨ fst , x ∷ snd ⟩} tT tS translG/z sat = {!   !} -- ⊗R M12 M23 M {!   !} (𝟙R {!   !}) ⊤R

  -- sat𝕀⟨𝔾⟩⇒proof tT tS translG/s sat = {!   !}
  {-
    This is the main theorem we want to prove. If we have a planning solution, we have a proof of
    the problem's translation.
  -}
  -- correctness : ∀ { P : Plan } { 𝕀 ℙ : List Condition } { 𝕋 : List STRIPSTerm } { 𝕆 : List Operator } { 𝔾 : Goal }
  --   { 𝕋ᵗ : Vec AdjointTerm (Data.List.length 𝕋)} { 𝕀ᵗ : Vec (Prop × Mode) (Data.List.length ℙ) } { 𝔾ᵗ : Prop × Mode } { 𝕆ᵗ : Vec (Prop × Mode) (Data.List.length 𝕆) }
  --   { Γ : Context (Data.Vec.length 𝕋ᵗ) (Data.Vec.length 𝕆ᵗ) } { Δ : Context 0 (Data.Vec.length 𝕀ᵗ) }   
  --   → TranslTs 𝕋 𝕋ᵗ
  --   → TranslS 𝕀 ℙ 𝕀ᵗ
  --   → TranslOs 𝕆 𝕆ᵗ
  --   → TranslG 𝔾 𝔾ᵗ
  --   → Contextify 𝕋ᵗ 𝕆ᵗ Γ
  --   → Contextify [] 𝕀ᵗ Δ
  --   → Solves 𝕀 P 𝔾
  --   → (Γ ++ᶜ Δ) ⊢ⁱ 𝔾ᵗ
   
  -- correctness tT tS tO tG cΓ cΔ (solves/z x) = sat𝕀⟨𝔾⟩⇒proof tT tS tG x 
  -- correctness _ _ _ _ _ _ (solves/s plan-solves x) = {!   !}   

  -- Some helper functions
      
  
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
    = ⊗-assoc (⊗R {!   !} {!   !} {!   !} {!   !} (id {!   !} {!   !}) (sat𝕀⟨𝔾⟩⇒proof P' sat'))
      where
        -- For the IH, we need proof that the initial state of P still satisfies the goal even after we've removed a condition of the goal
        P = record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = [] ; neg = (x ∷ neg) } }
        P' = record { PlanProblem P ; goals = record { pos = [] ; neg = neg } }
        
        sat' : sat (PlanProblem.initialState P') ⟨ [] , neg ⟩ 
        sat' = ⟨ (λ p x₁ → proj₁ sats p x₁), (λ p x₁ x₂ → proj₂ sats p (there x₁) x₂) ⟩
        
        𝕘 : Prop
        𝕘 = ` v[ translC x , term "false" ]

        Δₛ = contextify-state P
        Δₒ = contextify-operators P

        gInState : ⟨ 𝕘 , Linear ⟩ ∈ (proj₂ Δₛ)
        gInState = {!   !}

        IΔ = makeAllIrrelExcept ⟨ 𝕘 , Linear ⟩ Δₛ gInState  
        

  sat𝕀⟨𝔾⟩⇒proof record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = (x ∷ pos) ; neg = [] } } sat = {!   !}
  sat𝕀⟨𝔾⟩⇒proof record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = record { pos = (x ∷ pos) ; neg = (x₁ ∷ neg) } } sat = {!   !}
    
  correctness : ∀ { P : PlanProblem } { Τ : Plan }
    → Solves (PlanProblem.initialState P) Τ (PlanProblem.goals P)
    → translProb P

  correctness { P = P } (solves/z x) = sat𝕀⟨𝔾⟩⇒proof P x
  correctness (solves/s sol x) = {!   !}
     