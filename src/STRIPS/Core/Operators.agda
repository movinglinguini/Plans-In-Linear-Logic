open import Data.List
open import Data.Bool
open import Data.Unit
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable

module STRIPS.Core.Operators where
  open import STRIPS.Core.Conditions
  
  record Operator : Set where
    field
      posPre : List (Condition)
      negPre : List (Condition)
      posPost : List (Condition)
      negPost : List (Condition)

  variable
    o o₁ o₂ τ τ₁ τ₂ : Operator

  {- Syntactic Sugar -}
  infix 50 _⁺ _⁻ _₊ _₋

  _⁺ : Operator → List Condition
  o ⁺ = Operator.posPre o

  _⁻ : Operator → List Condition
  o ⁻ = Operator.negPre o

  _₊ : Operator → List Condition
  o ₊ = Operator.posPost o

  _₋ : Operator → List Condition
  o ₋ = Operator.negPost o

  {- Operator Properties -}
  isGroundOperatorᵇ : Operator → Bool
  isGroundOperatorᵇ o = (conditionsGround (Operator.posPre o)) ∧ ((conditionsGround (Operator.negPre o)) ∧ ((conditionsGround (Operator.posPost o)) ∧ (conditionsGround (Operator.negPost o))))
    where
      conditionsGround : List Condition → Bool
      conditionsGround ℂ = foldr (λ x acc → acc ∧ (isGroundConditionᵇ x)) true ℂ

  isGroundOperator : Operator → Set
  isGroundOperator o = T (isGroundOperatorᵇ o)

  isGroundOperator? : ∀ ( o : Operator ) → Dec (isGroundOperator o)
  isGroundOperator? o with isGroundOperatorᵇ o
  ... | false = no (λ ())
  ... | true = yes tt

  data WFOperator : Operator → Set where
    wf/operator : Disjoint (Operator.posPre o) (Operator.negPre o) → Disjoint (Operator.posPost o) (Operator.negPost o)  
      → WFOperator o