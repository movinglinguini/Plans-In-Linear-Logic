open import Data.Product
open import Data.Nat
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.Any
open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Bool

module STRIPS.Core.Goals where
  open import STRIPS.Core.Conditions

  -- A well-formed goal is one where all its conditions are in the problem condition vector.
  
  data Goals : ∀ { n } ( ℂ : Vec GroundCondition n ) → ( gs : List (GroundCondition × Bool) ) → Set where
    wf/goal/z : ∀ { n } { ℂ : Vec GroundCondition n } → Goals ℂ []

    wf/goal/s : ∀ { n g gs } { ℂ : Vec GroundCondition n } 
      → Goals ℂ gs → (wfcond : (proj₁ g) ∈ ℂ)
        ------------------------------------
      → Goals ℂ (g ∷ gs)  
 

  -- Example
  private
    ℂ : Vec GroundCondition 2
    ℂ = (record { label = "cond-1" ; terms = [] }) ∷ ((record { label = "cond-2" ; terms = [] }) ∷ [])

    gs : List (GroundCondition × Bool)
    gs = ((record { label = "cond-2" ; terms = [] }) , false) ∷ (((record { label = "cond-1" ; terms = [] }) , true) ∷ [])

    goals : Goals ℂ gs
    goals = wf/goal/s (wf/goal/s wf/goal/z (here refl)) (there (here refl))