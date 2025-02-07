open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.String
open import Data.Vec
open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Unit
open import Data.List.Membership.Propositional hiding (_∈_)
open import Data.Vec.Membership.Propositional hiding (_∉_)
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Bounded.Base using (Vec≤)
open import Relation.Nullary.Negation

open import Utils.Variables

module STRIPS.Core.Conditions (TermAtom : Set) where
  open import STRIPS.Core.Terms TermAtom

  record Condition : Set where 
    field 
      {argLength} : ℕ
      name : String
      args : Vec Term argLength

  variable
    p p₁ p₂ : Condition
    ℂ₁ ℂ₂ : List Condition

  {- Operations on conditions -}
  varArgsOf : ∀ ( p : Condition ) → Vec≤ Term (Condition.argLength p)
  varArgsOf record { name = name ; args = args } = Data.Vec.filter (isConst?) args

  ground : ∀ ( p : Condition ) ( T : Vec≤ Term (Condition.argLength p) ) 
    → All isConst (Vec≤.vec T) 
    → Condition
  ground record { name = name ; args = args } T allConstant = record { name = name ; args = groundVec args (Vec≤.vec T) }
    where
      groundVec : ∀ { n y } (args : Vec Term n) ( T : Vec Term y ) →  Vec Term n
      groundVec args [] = args
      groundVec [] (x ∷ T) = []
      groundVec (term a ∷ args) (x ∷ T) = (term a) ∷ (groundVec args (x ∷ T))
      groundVec (var a ∷ args) (x ∷ T) = x ∷ (groundVec args T)

  {- Properties of conditions -}
  isGroundConditionᵇ : Condition → Bool
  isGroundConditionᵇ p = Data.List.foldr (λ x acc → acc ∧ (isConstᵇ x)) true (Data.Vec.toList (Condition.args p))

  isGroundCondition : Condition → Set
  isGroundCondition p = T (isGroundConditionᵇ p)

  isGroundConditionᵇ? : ∀ (p : Condition) → Dec (isGroundCondition p)
  isGroundConditionᵇ? p with isGroundConditionᵇ p
  ... | false = no (λ ())
  ... | true = yes tt

  {- Properties of sets of conditions -}
  _∈ᶜᵇ_ : Condition → List Condition → Bool
  p ∈ᶜᵇ [] = false
  p ∈ᶜᵇ (x ∷ ℂ) = (does ((Condition.name p) Data.String.≟ (Condition.name x)) ∧ does ((Condition.argLength p) Data.Nat.≟ (Condition.argLength x))) ∨ (p ∈ᶜᵇ ℂ)

  data Disjoint : List Condition → List Condition → Set where
    dis/conds/z : Disjoint [] []

    dis/conds/s : p₁ ∉ ℂ₂ → p₂ ∉ ℂ₁ → Disjoint ℂ₁ ℂ₂ 
      → Disjoint (p₁ ∷ ℂ₁) (p₂ ∷ ℂ₂) 
   