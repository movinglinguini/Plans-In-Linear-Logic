open import Data.List
open import Data.Vec hiding ([]; fromList)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Relation.Nullary.Decidable
open import Data.Product
open import Data.Bool

module STRIPS.Core.States where
  open import STRIPS.Core.Conditions

  State = List (GroundCondition × Bool)  

  -- A state is well-formed if all of its conditions can be found in the problem conditions
  data WfState : State → List GroundCondition → Set where
    wf/state/z : ∀ { C } → WfState [] C
    wf/state/s : ∀ { s S C }
      → WfState S C   →   (proj₁ s) ∈ C
      → WfState (s ∷ S) C