open import Data.List
open import Relation.Binary.Definitions using (DecidableEquality)

module STRIPS.Core.Operators (Term : Set) where
  open import STRIPS.Core.Conditions Term
  -- open import Utils.ListUnion _≟ᶜ_

  record Operator : Set where
    field
      posPre : List (Condition)
      negPre : List (Condition)
      posPost : List (Condition)
      negPost : List (Condition)

  -- conds : Operator → List (Condition Term)
  -- conds o = (((Operator.posPre o) ∪ (Operator.negPre o)) ∪ (Operator.posPost o)) ∪ (Operator.negPost o)

  variable
    o o₁ o₂ : Operator

  private
    postulate
      posPre1 : Condition
      posPre2 : Condition
      negPost : Condition
    
    testOperator : Operator
    testOperator = record { posPre = posPre1 ∷ posPre2 ∷ [] ; negPre = [] ; posPost = [] ; negPost = negPost ∷ [] }
