open import Data.List
open import Data.Vec hiding (foldr)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Relation.Nullary.Negation

module STRIPS.Core.Sat where
  open import STRIPS.Core.Goals
  open import STRIPS.Core.States
  open import STRIPS.Core.Transitions
  open import STRIPS.Core.Operators

  -- A state satisfies a goal if all conditions in the goal can be found
  -- in the state.
  data Sat : State → Goal → Set where
    sat/z : ∀ { S }
      → Sat S []
    sat/s : ∀ { S g G }
      → Sat S G   →   g ∈ S
      → Sat S (g ∷ G)

  -- We say a state satisfies a transition if all of the conditions of the
  -- transition's preconditions can be found in the state.
  sat-τ : ∀ { ℂ 𝕆 } → State → Transition ℂ 𝕆 → Set
  sat-τ S (wf/transition o ts x x₁) = Sat S (pres gτ)
    where
      ground[τ] : GroundOperator
      ground[τ] = ground o ts

      gτ : Operator
      gτ = toOperator ground[τ] 