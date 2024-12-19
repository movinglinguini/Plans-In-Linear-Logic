open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Plans.Domain 

module Utils.WorldState (domain : Domain) where
  open Domain domain
  open import Plans.Semantics domain

  -- Transforms a state to a world by extracting the predicate
  -- of positive predmaps from the state
  stateToWorld : State → World
  stateToWorld [] = [] 
  stateToWorld ((polarity , pred) ∷ s) with polarity
  ... | + = pred ∷ (stateToWorld s)
  ... | - = stateToWorld s

  private 
    _ : stateToWorld [] ≡ []
    _ = refl

    postulate
      p1 : Predicate
      p2 : Predicate

    state : State
    state = (+ , p1) ∷ (- , p2) ∷ []
    
    _ : stateToWorld state ≡ (p1 ∷ [])
    _ = refl


  open import Data.List.Membership.DecPropositional _≟ₚ_ public using (_∈?_)
  
  worldToState : World → World → State
  worldToState w₁ [] = []
  worldToState w₁ (w ∷ w₂) with w ∈? w₁
  ... | yes _ = (+ , w) ∷ (worldToState w₁ w₂)
  ... | no _ = (- , w) ∷ (worldToState w₁ w₂)


  private    
    postulate
      p3 : Predicate
    
    _ : worldToState (p1 ∷ p3 ∷ []) [] ≡ []
    _ = refl