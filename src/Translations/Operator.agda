-- Translation of action descriptions from Actions You Can Handle into open 
-- lolli propositions in Adjoint Logic

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool hiding (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Plans.Domain
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

module Translations.Operator (domain : Domain) where
  open Domain domain
  open import ADJ.Core PredMap
  open import Data.List using (_++_; filterᵇ)

  private 
    cond : ActionDescription → List (Polarity × Predicate)
    cond record { preconditions = preconditions ; effects = effects } = preconditions ++ effects

    isPos : PredMap → Bool
    isPos ⟨ + , p ⟩ = true
    isPos ⟨ - , p ⟩ = false

    isNeg : PredMap → Bool
    isNeg p with isPos p
    ... | true = false
    ... | false = true

    filterPositive : List PredMap → List PredMap
    filterPositive L = filterᵇ isPos L
        
    filterNegative : List PredMap → List PredMap
    filterNegative L = filterᵇ isNeg L

    _≟_ : DecidableEquality PredMap
    ⟨ + , p₁ ⟩ ≟ ⟨ + , p₂ ⟩ with p₁ ≟ₚ p₂
    ... | yes p=p = yes {!   !} 
    ... | no p!=p = no {!   !}
    ⟨ - , p₁ ⟩ ≟ ⟨ + , p₂ ⟩ = no λ()
    ⟨ + , p₁ ⟩ ≟ ⟨ - , p₂ ⟩ = no λ()
    ⟨ - , p₁ ⟩ ≟ ⟨ - , p₂ ⟩ with p₁ ≟ₚ p₂
    ... | yes p=p = yes {!  !}
    ... | no p!=p = no {!   !}
  
  translO : ActionDescription → Prop U
  translO = {! Up[U](P₁ ⊸ P₂) !}
    where
      P₁ : Prop L
      P₂ : Prop L

      P₁ = {!   !}
      P₂ = {!   !}

      translP : PredMap → ActionDescription → (Predicate × Predicate)
      translP p o = {!   !}  