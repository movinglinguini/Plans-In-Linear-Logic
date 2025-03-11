open import Data.List
open import Data.Vec
open import Data.Maybe
open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable

module STRIPS.Core.Plans where
  open import STRIPS.Core.Operators
  open import STRIPS.Core.Goals
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Common
  
  -- A plan is just a list of ground operators
  Plan = List GroundOperator

  private 
    variable
      goalSize : ℕ
      Τ : Plan
      𝕀 : State
      𝔾 : Goal goalSize
      τ : GroundOperator
  
  {- Well-typed plan -}
  data Solves : ∀ { n } → State → Plan → Goal n → Set where
    -- If the given state already satisfies the plan, then the plan is empty.
    solves/z : sat 𝕀 ⟨ (toList (Goal.pos 𝔾)) , (toList (Goal.neg 𝔾)) ⟩
      → Solves 𝕀 [] 𝔾

    -- Given a state 𝕀 and a goal 𝔾, a plan solves the problem if 
    -- 1. the preconditions of the transition τ at the head of the plan is satisfied
    -- 2. the state given by updating 𝕀 with the postconditions of τ gets us closer
    --    to solving the problem.
    solves/s : Solves (update τ 𝕀) Τ 𝔾
      → sat 𝕀 ⟨ GroundOperator.posPre τ , GroundOperator.negPre τ ⟩
      → Solves 𝕀 (τ ∷ Τ) 𝔾 

