open import Data.List
open import Data.Vec
open import Data.Vec.Membership.Propositional

module STRIPS.Core.States where
  open import STRIPS.Core.Conditions

  data States : ∀ { n } → Vec GroundCondition n → List GroundCondition → Set where
    wf/state/z : ∀ { n } { ℂ : Vec GroundCondition n }
      → States ℂ []
    
    wf/state/s : ∀ { n c cs } { ℂ : Vec GroundCondition n }
      → States ℂ cs   →   c ∈ ℂ
      → States ℂ (c ∷ cs)
