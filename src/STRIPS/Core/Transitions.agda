open import Data.Vec hiding (remove)
open import Data.Vec.Membership.Propositional
open import Data.List
open import Data.Nat

open import STRIPS.Core.Operators
open import STRIPS.Core.Terms
open import STRIPS.Core.Conditions

module STRIPS.Core.Transitions where

  private
    variable
      n : ℕ
      o : Operator
      𝕋 : Vec TermConstant n
      ts : Vec TermConstant (Operator.arity o)

  data Transition : ∀ { n } → ( o : Operator ) → Vec TermConstant (Operator.arity o) → Vec TermConstant n → Set where
    wf/transition : ∀ { n } → ( o : Operator ) ( ts : Vec TermConstant (Operator.arity o) ) ( 𝕋 : Vec TermConstant n )
      → (∀ t → t ∈ ts → t ∈ 𝕋)
      → Transition o ts 𝕋

  ground : Transition o ts 𝕋 → GroundOperator
  ground (wf/transition o [] _ _) = {!   !}
  ground (wf/transition o (x ∷ ts) _ _) = {!   !}

  {- The Update Function -}
  update : Transition o ts 𝕋 → State → State
  -- update τ S = add (remove S (GroundOperator.negPost τ)) (GroundOperator.posPost τ)
  --   where
  --     add : State → List (Condition 0) → State
  --     add 𝕊 A = A ∪ᶜ 𝕊

  --     remove : State → List (Condition 0) → State
  --     remove [] R = [] 
  --     remove 𝕊 [] = 𝕊
  --     remove (s ∷ 𝕊) R with s ∈ᶜᵇ R
  --     ... | false = s ∷ remove 𝕊  R 
  --     ... | true = remove 𝕊 R  
