open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.String hiding (toList) renaming (_≟_ to _≟ˢ_)
open import Data.Vec hiding (foldr)
open import Data.Nat renaming (_≟_ to _≟ⁿ_)
open import Data.Fin
open import Data.List
open import Data.Bool
open import Data.Unit
open import Data.List.Membership.Propositional hiding (_∈_)
open import Data.Vec.Membership.Propositional hiding (_∉_)
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Bounded.Base using (Vec≤)
open import Relation.Nullary.Negation

open import Utils.Variables

module STRIPS.Core.Conditions where
  open import STRIPS.Core.Terms

  record Condition ( Scope : ℕ ) : Set where 
    field
      name : String
      terms : List (Term Scope)

  -- State is just a list of Conditions with 0 scope
  State = List (Condition 0)

  {- Properties of sets of conditions -}

  -- Boolean equality over conditions. This is basically syntactic equality squashed to the
  -- level of booleans
  _≟ᶜᵇ_ : ∀ { s } ( c₁ c₂ : Condition s ) → Bool
  c₁ ≟ᶜᵇ c₂ = (does ((Condition.name c₁) ≟ˢ (Condition.name c₂))) 
              ∧ ((Condition.terms c₁) ≗ᵗ (Condition.terms c₂))

  -- Let's test this equality
  private
    c₁ : Condition 2
    c₁ = record { name = "test-condition" ; terms = var zero ∷ var (suc (zero)) ∷ const "const" ∷ [] } 
    c₂ : Condition 2
    c₂ = record { name = "test-condition" ; terms = var zero ∷ var (suc (zero)) ∷ const "const" ∷ [] } 

    -- c₁ and c₂ are syntactically equivalent, so we expect them to be boolean equivalent
    _ : c₁ ≟ᶜᵇ c₂ ≡ true
    _ = refl

    -- c₃ is different from the other two syntactically, so we expect the comparison to return false
    c₃ : Condition 2
    c₃ = record { name = "test-condition" ; terms = var zero ∷ const "const" ∷ const "const" ∷ [] } 
    _ : c₃ ≟ᶜᵇ c₂ ≡ false
    _ = refl

  -- {- Operations on vectors of conditions -}
  
  -- List membership squashed to the level of bools
  -- A condition is a member of a list of conditions if it is syntactically
  -- equivalent to at least one.
  _∈ᶜᵇ_ : ∀ { s } → Condition s → List (Condition s) → Bool 
  c ∈ᶜᵇ [] = false
  c ∈ᶜᵇ (x ∷ C) = (x ≟ᶜᵇ c) ∨ (c ∈ᶜᵇ C)

  -- Union
  _∪ᶜ_ : ∀ { s } → List (Condition s) → List (Condition s) → List (Condition s)
  [] ∪ᶜ C₂ = C₂
  (c ∷ C₁) ∪ᶜ C₂ with c ∈ᶜᵇ (C₂)
  ... | false = c ∷ (C₁ ∪ᶜ C₂)
  ... | true = C₁ ∪ᶜ C₂

  -- Intersection
  _∩ᶜ_ : ∀ { s } → List (Condition s) → List (Condition s) → List (Condition s)
  [] ∩ᶜ C₂ = []
  (x ∷ C₁) ∩ᶜ C₂ with x ∈ᶜᵇ C₂
  ... | false = C₁ ∩ᶜ C₂
  ... | true = x ∷ C₁ ∩ᶜ C₂