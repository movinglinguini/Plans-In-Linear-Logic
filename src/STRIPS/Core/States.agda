open import Data.List
open import Data.Vec
open import Data.Vec.Membership.Propositional

module STRIPS.Core.States where
  open import STRIPS.Core.Conditions

  data States : ∀ { n } → List GroundCondition → Vec GroundCondition n → Set where
    wf/state/z : ∀ { n } { ℂ : Vec GroundCondition n }
      → States [] ℂ
    
    wf/state/s : ∀ { n c cs } { ℂ : Vec GroundCondition n }
      → States cs ℂ   →   c ∈ ℂ
      → States (c ∷ cs) ℂ
