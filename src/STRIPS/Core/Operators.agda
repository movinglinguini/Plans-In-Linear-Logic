open import Data.List
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Data.Vec hiding (remove)
open import Data.String
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable

module STRIPS.Core.Operators where
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Terms
  
  -- An operator comes with its own scope and arity
  record Operator : Set where
    field
      label : String
      arity : ℕ
      posPre : List (Condition arity)
      negPre : List (Condition arity)
      posPost : List (Condition arity)
      negPost : List (Condition arity)

  {- Some syntactic sugar for extracting parts of operators -}
  infix 50 _⁺ _⁻ _₊ _₋

  -- Positive preconditions
  _⁺ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁺ = Operator.posPre o

  -- Negative preconditions
  _⁻ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁻ = Operator.negPre o

  -- Positive postconditions
  _₊ : (o : Operator) → List (Condition (Operator.arity o))
  o ₊ = Operator.posPost o

  -- Negative postconditions
  _₋ : (o : Operator) → List (Condition (Operator.arity o))
  o ₋ = Operator.negPost o

  -- All preconditions
  pres : (o : Operator) → List (Condition (Operator.arity o))
  pres o = (Operator.posPre o) ∪ᶜ (Operator.negPre o)

  -- All postconditions
  posts : (o : Operator) → List (Condition (Operator.arity o))
  posts o = (Operator.posPost o) ∪ᶜ (Operator.negPost o)

  {--
  - Ground Operators
  --}

  record GroundOperator : Set where
    field
      label : String
      posPre : List (Condition 0)
      negPre : List (Condition 0)
      posPost : List (Condition 0)
      negPost : List (Condition 0)

  {- The Update Function -}
  update : GroundOperator → State → State
  update τ S = add (remove S (GroundOperator.negPost τ)) (GroundOperator.posPost τ)
    where
      add : State → List (Condition 0) → State
      add 𝕊 A = A ∪ᶜ 𝕊

      remove : State → List (Condition 0) → State
      remove [] R = [] 
      remove 𝕊 [] = 𝕊
      remove (s ∷ 𝕊) R with s ∈ᶜᵇ R
      ... | false = s ∷ remove 𝕊 R 
      ... | true = remove 𝕊 R