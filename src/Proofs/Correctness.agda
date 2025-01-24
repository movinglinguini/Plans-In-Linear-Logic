open import Data.List using (List; _∷_; []; map)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Plans.Domain
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)

module Proofs.Correctness (domain : Domain) where

  open Domain domain
  open import Plans.Plan domain
  open import Plans.Semantics domain
  
  -- Syntax
  open import Syntax.Core domain

  -- Translations
  open import Translations.State domain
  open import Translations.Operator domain
  open import Translations.Goal domain

  -- ADJ
  open import ADJ.Core Proposition Term renaming (Context to Ctxt)

  open import Utils.PlanToList domain
  open import Utils.WorldState domain
  open import Utils.BigTensor Proposition Term
  open import Utils.ListToContext Proposition Term
  -- lem-1 : ∀ { τ s S' P } ( S : State ) (St : List (Prop Linear)) (Pt : List (Prop Linear))
  --       → S ≡ (s ∷ S')
  --       → P ≡ ActionDescription.preconditions τ
  --       → St ≡ translS S
  --       → Pt ≡ translS P 
  --       → (stateToWorld S) ∈⟨ P ⟩ 
  --       → (∀ { pt } → pt ∈ Pt → pt ∈ St)

  -- lem-1 {τ} {s} {S'} {P} S St [] S-split P-isPrecond S-transl P-transl S-sat ()
  -- lem-1 {τ} {s} {S'} {p ∷ P} S St ((` v[ p[t] , true ]) ∷ Pt) S-split P-isPrecond S-transl P-transl S∈⟨P⟩ pt∈Pt = {! !}
  --   where
  --     translp-is-true : translPredmap p ≡ v[ p[t] , true ]
  --     translp-is-true = {!   !}

  --     p-is-+ : p ≡ ⟨ + , p[t] ⟩
  --     p-is-+ = invert-pos-case translp-is-true

      

  -- lem-1 {τ} {s} {S'} {p ∷ P} S St ((` v[ x , false ]) ∷ Pt) S-split P-isPrecond S-transl P-transl S∈⟨P⟩ pt∈Pt = {!   !}
  -- lem-1 {τ} {s} {S'} {p ∷ P} S St ((` v[ x , var x₁ ]) ∷ Pt) S-split P-isPrecond S-transl P-transl S∈⟨P⟩ pt∈Pt = {!   !}
  --     where

  {-
    Helper functions
  -}
  translContext : ∀ ( Γ : Domain.Context domain ) ( P : List Action ) → List (Prop Unrestricted)
  translContext Γ P = Data.List.map (λ α → translO (Γ α)) P

  lemma:state-⊗ : ∀ (W : World) (Wt : World) (S : State) 
                  → W ∈⟨ S ⟩
                  → listToContext (translS (worldToState W Wt)) ⊢ (⨂(translS S)) ⊗ ⊤
  lemma:state-⊗ W Wt S W∈⟨S⟩ = {!   !} 

  lemma:empty-plan : ∀ { Γ : Domain.Context domain } { 𝕀 : World } { 𝕀T : World } { 𝔾 : GoalState }
                  → Γ ⊢ halt ∶ 𝕀 ↝ 𝔾
                  → listToContext (translS (worldToState 𝕀 𝕀T)) ++ (listToContext (translContext Γ [])) ⊢ translG 𝔾 ⊗ ⊤

  lemma:empty-plan {_} {_} {_} {[]} (halt 𝕀∈⟨[]⟩) = {!   !}
  lemma:empty-plan {_} {𝕀} {𝕀T} {𝕘 ∷ 𝔾} (halt 𝕀∈⟨𝔾⟩) = {!   !}
    where
      𝕘t : Prop Linear
      𝕘t = Prop.` translPredmap 𝕘

  {-
    If a plan ℙ is valid for a given problem (defined by initial state 𝕀, goal state 𝔾, and action context Γ),
    then its translation into a DILL sequent is derivable.
  -}
  correctness : ∀ ( ℙ : Plan ) ( Γ : Domain.Context domain ) ( 𝕀 : World ) (𝕀T : World) ( 𝔾 : GoalState )
                  → Γ ⊢ ℙ ∶ 𝕀 ↝ 𝔾
                  → listToContext (translS (worldToState 𝕀 𝕀T)) ++ listToContext (translContext Γ (planToList ℙ)) ⊢ translG 𝔾 ⊗ ⊤

  -- In the halt case, we need to show that since 𝕀 already satisfies 𝔾, then the translation
  -- of 𝕀 is enough to prove the translation of the goal state.
  correctness halt Γ 𝕀 𝕀T 𝔾 ℙ-isvalid = lemma:empty-plan { Γ } { 𝕀 } ℙ-isvalid
  correctness (α ∷ ℙ) Γ 𝕀 𝕀T 𝔾 ℙ-isvalid = {!   !}

  
   
         
         