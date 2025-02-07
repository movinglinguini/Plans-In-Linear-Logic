open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.String
open import Data.Vec
open import Data.Nat
open import Data.List
open import Data.List.Membership.Propositional

open import Utils.Variables

module STRIPS.Core.Conditions (Term : Set) where   
  record Condition : Set where 
    field
      name : String
      argLength : ℕ
      args : Vec Term argLength

  variable
    p₁ p₂ : Condition
    ℂ₁ ℂ₂ : List Condition

  private
    -- Example condition: p(t₁, t₂, t₃)
    postulate
      t₁ t₂ t₃ : Term

    testCondition : Condition
    testCondition = record { name = "p" ; argLength = 3 ; args = t₁ ∷ t₂ ∷ t₃ ∷ [] }

  data Disjoint : List Condition → List Condition → Set where
    dis/conds/z : Disjoint [] []

    dis/conds/s : p₁ ∉ ℂ₂ → p₂ ∉ ℂ₁ → Disjoint ℂ₁ ℂ₂ 
      → Disjoint (p₁ ∷ ℂ₁) (p₂ ∷ ℂ₂) 
