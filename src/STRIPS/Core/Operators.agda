open import Data.List
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Vec hiding (remove)
open import Data.Vec.Membership.Propositional
open import Data.String
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable

open import STRIPS.Core.Common
open import STRIPS.Core.Conditions
open import STRIPS.Core.Terms

module STRIPS.Core.Operators where

  {- 
    Definition of operators

    We see operators as lists of tuples ⟨ c , b , p ⟩, where c is a condition, b
    is the condition's boolean value, and p is the condition's position. The boolean
    value determines the condition's "polarity" (not in the type theoretic sense). The position
    denotes whether the condition is a precondition or a postcondition. For example,
    ⟨ c , true , precond ⟩ denotes a positive precondition, while ⟨ c , false, postcond ⟩ denotes
    a negative postcondition. 
  -}

  -- The condition position denotes whether the condition is a precondition or a postcondition
  data OperatorConditionPosition : Set where
    precond : OperatorConditionPosition
    postcond : OperatorConditionPosition
  
  {- Operators on condition positions -}
  _≟cp_ : OperatorConditionPosition → OperatorConditionPosition → Bool
  precond ≟cp precond = true
  precond ≟cp postcond = false
  postcond ≟cp precond = false
  postcond ≟cp postcond = true

  -- An operator condition is a tuple that contains a condition of arbitrary arity, a boolean
  -- and a position.
  data OperatorCondition : ℕ → Set where
    opcond : ∀ { arity } → ((Condition arity) × Bool) → OperatorConditionPosition → OperatorCondition arity
  
  -- An operator packages up a list of OperatorConditions of arbitrary arity with a label
  -- data Operator : ∀ { n } → Vec String n → Set where
  --   op : ∀ { n } { legalNames : Vec String n } arity 
  --     → (label : String) → label ∈ legalNames
  --     → (List (OperatorCondition arity)) 
  --     → Operator
  record Operator : Set where
    field
      label : String
      arity : ℕ
      conds : List (OperatorCondition arity)

  {-
   Extracting data from operators
  -}

  -- Getting preconditions of o
  private
    extract-CondPairs : ∀ { a } → List (OperatorCondition a) → OperatorConditionPosition → List ((Condition a) × Bool)
    extract-CondPairs [] _ = []
    extract-CondPairs (opcond cp pos₁ ∷ ocs) pos₂ with pos₁ ≟cp pos₂
    ... | false = extract-CondPairs ocs pos₂
    ... | true = cp ∷ extract-CondPairs ocs pos₂
  
  pres : (o : Operator) → List ((Condition (Operator.arity o)) × Bool)
  pres o = extract-CondPairs (Operator.conds o) precond

  posts : (o : Operator) → List ((Condition (Operator.arity o)) × Bool)
  posts o = extract-CondPairs (Operator.conds o) postcond

  -- Getting just conditions from preconditions of o
  _⁺ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁺ = getPositives (pres o)

  _⁻ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁻ = getNegatives (pres o)

  _₋ : (o : Operator) → List (Condition (Operator.arity o))
  o ₋ = getNegatives (posts o)

  _₊ : (o : Operator) → List (Condition (Operator.arity o))
  o ₊ = getPositives (posts o)

  {--
    Ground Operators are operators with all ground conditions.
  --}
  record GroundOperator : Set where
    field
      label : String
      conds : List (OperatorCondition 0)

  {- Operations on ground operators -}
  toOperator : GroundOperator → Operator
  toOperator g = record { label = GroundOperator.label g ; arity = 0 ; conds = GroundOperator.conds g }

  {- 
    The grounding function. This transforms an operator into a ground operator
    by substituting variable terms.
  -}
  private
    subst-Term : ∀ { s } → Term (suc s) → TermConstant → Term s
    subst-Term (const x) _ = const x
    subst-Term (var zero) (const x) = const x
    subst-Term (var (suc m)) (const x) = var m

    subst-Terms : ∀ { s } → List (Term (suc s)) → TermConstant → List (Term s)
    subst-Terms [] t = []
    subst-Terms (x ∷ ts) t = (subst-Term x t) ∷ (subst-Terms ts t)

    subst-Condition : ∀ { s } → Condition (suc s) → TermConstant → Condition s
    subst-Condition C t = record { Condition C ; terms = subst-Terms (Condition.terms C) t }
    
    ground-Condition : ∀ { s } → Condition s → Vec TermConstant s → GroundCondition
    ground-Condition c [] = c
    ground-Condition c (t ∷ ts) = 
      let c' = subst-Condition c t
        in ground-Condition c' ts

    ground-ConditionPair : ∀ { s } → ((Condition s) × Bool) → Vec TermConstant s → GroundCondition × Bool
    ground-ConditionPair (fst , snd) ts = (ground-Condition fst ts) , snd
    
    ground-OperatorCondition : ∀ { s } → OperatorCondition s → Vec TermConstant s → OperatorCondition 0
    ground-OperatorCondition (opcond x x₁) ts = opcond (ground-ConditionPair x ts) x₁

    ground-OperatorConditions : ∀ { s } → List (OperatorCondition s) → Vec TermConstant s → List (OperatorCondition 0)
    ground-OperatorConditions [] ts = []
    ground-OperatorConditions (oc ∷ ocs) ts = (ground-OperatorCondition oc ts) ∷ (ground-OperatorConditions ocs ts)

  ground : (o : Operator) → Vec TermConstant (Operator.arity o) → GroundOperator
  ground o ts = record { label = (Operator.label o) ; conds = ground-OperatorConditions (Operator.conds o) ts }

  private
    variable
      n : ℕ
      ℂ : Vec GroundCondition n

  -- A ground operator is well-formed if all of its underlying conditions can be
  -- found in the list of problem conditions.
  data WfGroundOperator : ∀ { n } → GroundOperator → Vec GroundCondition n → Set where
    wf/groundop/z : ∀ { ℓ } → WfGroundOperator (record { label = ℓ ; conds = [] }) ℂ

    wf/groundop/s : ∀ { ℓ c ocs p b } 
      → WfGroundOperator (record { label = ℓ ; conds = ocs }) ℂ
      → c ∈ ℂ
      → WfGroundOperator (record { label = ℓ ; conds = (opcond (c , b) p) ∷ ocs }) ℂ