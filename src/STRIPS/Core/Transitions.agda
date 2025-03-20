open import Data.Vec hiding (remove)
open import Data.Vec.Membership.Propositional
open import Data.List
open import Data.Nat
open import Data.Fin

open import STRIPS.Core.Operators
open import STRIPS.Core.Terms
open import STRIPS.Core.Conditions
open import STRIPS.Core.States

module STRIPS.Core.Transitions where

  private
    variable
      n : ℕ
      o : Operator
      𝕋 : Vec TermConstant n
      ts : Vec TermConstant (Operator.arity o)


  -- A well-formed transition is one where 
  data Transition : ∀ { n } → ( o : Operator ) → Vec TermConstant (Operator.arity o) → Vec TermConstant n → Set where
    wf/transition : ∀ { n } → ( o : Operator ) ( ts : Vec TermConstant (Operator.arity o) ) ( 𝕋 : Vec TermConstant n )
      → (∀ t → t ∈ ts → t ∈ 𝕋)
      → Transition o ts 𝕋

  {-
    TODO : Write new update function that uses transitions rather than ground operators
  -}
