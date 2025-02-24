open import Data.List
open import Data.Bool
open import Data.Unit
open import Data.String
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable

module STRIPS.Core.Operators where
  open import STRIPS.Core.Conditions
  
  record Operator : Set where
    field
      label : String
      posPre : List (Condition)
      negPre : List (Condition)
      posPost : List (Condition)
      negPost : List (Condition)

  variable
    o o₁ o₂ τ τ₁ τ₂ : Operator
    O O₁ O₂ : List Operator

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

  pres : Operator → List Condition
  pres o = (Operator.posPre o) ∪ᶜ (Operator.negPre o)

  posts : Operator → List Condition
  posts o = (Operator.posPost o) ∪ᶜ (Operator.negPost o)

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

  {- The Update Function -}
  update : ∀ ( 𝕊 : List Condition ) ( 𝕠 : Operator ) → List Condition
  update 𝕊 𝕠 = add (remove 𝕊 (𝕠 ₋)) (𝕠 ₊)
    where
      add : List Condition → List Condition → List Condition
      add 𝕊 A = A ∪ᶜ 𝕊

      remove : List Condition → List Condition → List Condition
      remove [] R = [] 
      remove 𝕊 [] = 𝕊
      remove (s ∷ 𝕊) R with s ∈ᶜᵇ R
      ... | false = s ∷ remove 𝕊 R 
      ... | true = remove 𝕊 R