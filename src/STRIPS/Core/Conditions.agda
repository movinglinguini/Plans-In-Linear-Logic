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
open import Relation.Nullary.Reflects

open import Utils.Variables

open import STRIPS.Core.Terms

module STRIPS.Core.Conditions where

  record Condition ( Scope : ℕ ) : Set where 
    field
      label : String
      terms : List (Term Scope)

  private
    variable
      𝕃 : Vec String n

  GroundCondition = Condition 0

  {- Properties of sets of conditions -}

  -- Boolean equality over conditions. This is basically syntactic equality squashed to the
  -- level of booleans
  _≟ᶜᵇ_ : ∀ { s } ( c₁ c₂ : Condition s) → Bool
  c₁ ≟ᶜᵇ c₂ = (does ((Condition.label c₁) ≟ˢ (Condition.label c₂))) 
              ∧ ((Condition.terms c₁) ≗ᵗᵇ (Condition.terms c₂))

  -- Helper function for proving decidable equality over conditions.
  ≟ᶜ-lemma : ∀ { s } { c₁ c₂ : Condition s }
    → (Condition.label c₁) ≡ (Condition.label c₂)
    → (Condition.terms c₁) ≡ (Condition.terms c₂)
    → c₁ ≡ c₂
  ≟ᶜ-lemma refl refl = refl

  -- Decidable equality over conditions. 
  _≟ᶜ_ : ∀ { s } → DecidableEquality (Condition s)
  c₁ ≟ᶜ c₂ with (Condition.label c₁) ≟ˢ (Condition.label c₂) | (Condition.terms c₁) ≗ᵗ (Condition.terms c₂)
  ... | no ¬a | _ = no λ x → ¬a (cong Condition.label x) 
  ... | _ | no ¬a = no (λ x → ¬a (cong Condition.terms x))
  ... | yes a₁ | yes a₂ = yes (≟ᶜ-lemma a₁ a₂)

  -- Let's test this equality
  private
    c₁ : Condition 2
    c₁ = record { label = "test-condition" ; terms = var zero ∷ var (suc (zero)) ∷  const "const" ∷ [] } 
    c₂ : Condition 2
    c₂ = record { label = "test-condition" ; terms = var zero ∷ var (suc (zero)) ∷ const "const" ∷ [] } 

    -- c₁ and c₂ are syntactically equivalent, so we expect them to be boolean equivalent
    _ : c₁ ≟ᶜᵇ c₂ ≡ true
    _ = refl

    -- c₃ is different from the other two syntactically, so we expect the comparison to return false
    c₃ : Condition 2
    c₃ = record { label = "test-condition" ; terms = var zero ∷ const "const" ∷ const "const" ∷ [] } 
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

  {-
    Terms of a condition
  -}
  constantsOf : ∀ { s } → Condition s → List TermConstant
  constantsOf c = filterTerms (Condition.terms c)