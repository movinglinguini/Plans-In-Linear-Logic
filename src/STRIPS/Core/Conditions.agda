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

module STRIPS.Core.Conditions where
  open import STRIPS.Core.Terms

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
  varArgsOf record { name = name ; args = args } = Data.Vec.filter (isVar?) args

  countVars : Condition → ℕ
  countVars p = Data.Vec.length (Vec≤.vec (varArgsOf p))

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

  isGroundCondition? : ∀ (p : Condition) → Dec (isGroundCondition p)
  isGroundCondition? p with isGroundConditionᵇ p
  ... | false = no (λ ())
  ... | true = yes tt

  {- Properties of sets of conditions -}
  doSignaturesMatch : Condition → Condition → Bool
  doSignaturesMatch p₁ p₂ = does ((Condition.name p₁) Data.String.≟ (Condition.name p₂)) ∧ does ((Condition.argLength p₁) Data.Nat.≟ (Condition.argLength p₂))

  private
    p1 : Condition
    p2 : Condition
    p3 : Condition

    p1 = record { name = "test-condition" ; args = var 0 ∷ var 1 ∷ var 3 ∷ [] }
    p2 = record { name = "test-condition" ; args = var 0 ∷ var 1 ∷ var 3 ∷ [] }
    p3 = record { name = "test-condition" ; args = var 0 ∷ var 1 ∷ [] }

    _ : doSignaturesMatch p1 p2 ≡ true
    _ = refl

    _ : doSignaturesMatch p1 p3 ≡ false
    _ = refl

  {- Operations on lists of conditions -}
  _∈ᶜᵇ_ : Condition → List Condition → Bool
  p ∈ᶜᵇ [] = false
  p ∈ᶜᵇ (x ∷ ℂ) = (doSignaturesMatch p x) ∨ (p ∈ᶜᵇ ℂ)

  _∈ᶜ_ : Condition → List Condition → Set
  p ∈ᶜ ℂ = T (p ∈ᶜᵇ ℂ)

  _∉ᶜ_ : Condition → List Condition → Set
  p ∉ᶜ ℂ = ¬ (p ∈ᶜ ℂ)

  _∈ᶜ?_ : ( p : Condition ) ( ℂ : List Condition ) → Dec ( p ∈ᶜ ℂ )
  p ∈ᶜ? ℂ with p ∈ᶜᵇ ℂ
  ... | false = no (λ x → x)
  ... | true = yes tt

  -- Union
  _∪ᶜ_ : List Condition → List Condition → List Condition
  [] ∪ᶜ ℂ₂ = ℂ₂
  (p ∷ ℂ₁) ∪ᶜ ℂ₂ with does (p ∈ᶜ? ℂ₂)
  ... | false = p ∷ (ℂ₁ ∪ᶜ ℂ₂)
  ... | true = ℂ₁ ∪ᶜ ℂ₂
  
  -- Intersection
  _∩ᶜ_ : List Condition → List Condition → List Condition
  [] ∩ᶜ ℂ₂ = []
  (p ∷ ℂ₁) ∩ᶜ ℂ₂ with does (p ∈ᶜ? ℂ₂)
  ... | false = ℂ₁ ∩ᶜ ℂ₂
  ... | true = p ∷ ℂ₁ ∩ᶜ ℂ₂
  
  -- TODO: Rewrite this
  data Disjoint : List Condition → List Condition → Set where
    dis/conds/z : Disjoint [] []

    dis/conds/s : p₁ ∉ ℂ₂ → p₂ ∉ ℂ₁ → Disjoint ℂ₁ ℂ₂ 
      → Disjoint (p₁ ∷ ℂ₁) (p₂ ∷ ℂ₂) 
   