open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Maybe

open import Agda.Builtin.FromNat
import Data.Nat.Literals as NatLiterals
import Data.Fin.Literals as FinLiterals

open import MovieDomain
open import Plans.Semantics movieDomain
open import Plans.Plan movieDomain
open import Plans.ActionHandler movieDomain

module MovieExample where 
  instance
    NumFin : ∀ {n} → Number (Fin n)
    NumFin {n} = FinLiterals.number n

  initialWorld : World
  initialWorld = 
    (chips (id 0)) ∷
    (chips (id 1)) ∷
    (chips (id 2)) ∷
    (chips (id 3)) ∷
    (chips (id 4)) ∷
    (dip (id 0)) ∷
    (dip (id 1)) ∷
    (dip (id 2)) ∷
    (dip (id 3)) ∷
    (dip (id 4)) ∷
    (pop (id 0)) ∷
    (pop (id 1)) ∷
    (pop (id 2)) ∷
    (pop (id 3)) ∷
    (pop (id 4)) ∷
    (cheese (id 0)) ∷
    (cheese (id 1)) ∷
    (cheese (id 2)) ∷
    (cheese (id 3)) ∷
    (cheese (id 4)) ∷
    (crackers (id 0)) ∷
    (crackers (id 1)) ∷
    (crackers (id 2)) ∷
    (crackers (id 3)) ∷
    (crackers (id 4)) ∷
    (counter-at-other-than-two-hours) ∷
    []
  
  goalState : GoalState
  goalState = 
    (+ , movie-rewound) ∷
    (+ , counter-at-zero) ∷ 
    (+ , have-chips) ∷
    (+ , have-dip) ∷
    (+ , have-pop) ∷
    (+ , have-cheese) ∷
    (+ , have-crackers) ∷
    []

  planₜ : Plan
  planₜ = 
    (get-crackers (id 4)) ∷
    (get-cheese (id 4)) ∷
    (get-pop (id 4)) ∷
    (get-dip (id 4)) ∷
    (get-chips (id 4)) ∷
    (rewind-movie) ∷
    (reset-counter) ∷
    halt

  Derivation : Γ ⊢ planₜ ∶ initialWorld ↝ goalState
  Derivation = from-just (solver Γ planₜ initialWorld goalState)

  finalState : World
  finalState = execute planₜ (canonical-σ Γ) initialWorld

  -- Translation of goal state
  open import Translations.Goal movieDomain

  tGoal : Prop Linear 
  tGoal = translG goalState