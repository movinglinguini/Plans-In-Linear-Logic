open import Data.Vec hiding (remove)
open import Data.List.Membership.Propositional
open import Data.List
open import Data.Nat
open import Data.Fin
open import Data.Bool

open import STRIPS.Core.Operators
open import STRIPS.Core.Terms
open import STRIPS.Core.Conditions
open import STRIPS.Core.States

module STRIPS.Core.Transitions where
  private
    variable
      n m q : ℕ
      o : Operator
      S : List GroundCondition
      𝕋 : List TermConstant
      𝕆 : List Operator
      ℂ : List GroundCondition
      ts : Vec TermConstant (Operator.arity o)


  {- 
    Definition of a planning transition. A well-formed planning transition is
    a tuple ⟨ o , ts ⟩, where operator o is from the list of problem operators
    and grounding o with ts forms a well-formed ground operator.
  -}
  data Transition : 
      List GroundCondition
      → List Operator
      → Set where
    wf/transition : ( o : Operator ) → (ts : Vec TermConstant (Operator.arity o))
      → o ∈ 𝕆 
      → WfGroundOperator (ground o ts) ℂ
      → Transition ℂ 𝕆

  ground[_] : Transition ℂ 𝕆 → Operator
  ground[ wf/transition o ts _ _ ] = toOperator (ground o ts)

  {- Updating state -}
  -- Given a state S and transition τ, we define an update on S as follows:
  -- 1. let ground(τ) be the ground operator yielded by grounding the underlying operator
  --    of τ with the underlying terms of τ.
  -- 2. remove negative postconditions of ground(τ) from S
  -- 3. add positive postconditions of ground(τ) to S
  update : List GroundCondition → Transition ℂ 𝕆 → List GroundCondition
  update S (wf/transition o ts _ _) = add (remove S gτ-) gτ+
    where
      gτ : GroundOperator
      gτ = ground o ts

      gτ+ : List GroundCondition
      gτ+ = (toOperator gτ) ₊

      gτ- : List GroundCondition
      gτ- = (toOperator gτ) ₋

      add : List GroundCondition → List GroundCondition → List GroundCondition
      add S A = S ∪ᶜ A

      remove : List GroundCondition → List GroundCondition → List GroundCondition
      remove [] R = []
      remove (s ∷ S) [] = s ∷ S
      remove (s ∷ S) (r ∷ R) with s ∈ᶜᵇ (r ∷ R)
      ... | false = s ∷ remove S R
      ... | true = remove S R 