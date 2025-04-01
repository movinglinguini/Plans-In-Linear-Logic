open import Data.List
open import Data.Vec hiding ([]; fromList)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec.Membership.Propositional
open import Data.Maybe
open import Relation.Nullary.Decidable

module STRIPS.Core.States where
  open import STRIPS.Core.Conditions

  data State : ∀ { n } → List GroundCondition → Vec GroundCondition n → Set where
    wf/state/z : ∀ { n } { ℂ : Vec GroundCondition n }
      → State [] ℂ
    
    wf/state/s : ∀ { n c cs }  { ℂ : Vec GroundCondition n }
      → State cs ℂ   →   c ∈ ℂ
      → State (c ∷ cs) ℂ 
  
  open import Data.Vec.Membership.DecPropositional { A = GroundCondition } (_≟ᶜ_)
  wf-state? : ∀ { n } → (S : List GroundCondition) → (ℂ : Vec GroundCondition n) → Maybe (State S ℂ)
  wf-state? [] ℂ = just wf/state/z 
  wf-state? (s ∷ S) ℂ with s ∈? ℂ
  ... | no _ = nothing
  ... | yes mem with wf-state? S ℂ
  ...   | nothing = nothing
  ...   | just wf = just (wf/state/s wf mem) 