open import Data.List
open import Data.Vec hiding ([]; _∷_; fromList)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec.Membership.Propositional

module STRIPS.Core.States where
  open import STRIPS.Core.Conditions

  data State : ∀ { n } → List GroundCondition → Vec GroundCondition n → Set where
    wf/state/z : ∀ { n } { ℂ : Vec GroundCondition n }
      → State [] ℂ
    
    wf/state/s : ∀ { n c cs }  { ℂ : Vec GroundCondition n }
      → State cs ℂ   →   c ∈ ℂ
      → State (c ∷ cs) ℂ 
      