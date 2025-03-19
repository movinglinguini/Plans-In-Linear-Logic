open import Data.List
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (remove)
open import Data.String
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable

module STRIPS.Core.Operators where
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Terms
  
  -- An operator comes with its own scope and arity
  record Operator : Set where
    field
      label : String
      arity : ℕ
      posPre : List (Condition arity)
      negPre : List (Condition arity)
      posPost : List (Condition arity)
      negPost : List (Condition arity)

  {- Some syntactic sugar for extracting parts of operators -}
  infix 50 _⁺ _⁻ _₊ _₋

  -- Positive preconditions
  _⁺ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁺ = Operator.posPre o

  -- Negative preconditions
  _⁻ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁻ = Operator.negPre o

  -- Positive postconditions
  _₊ : (o : Operator) → List (Condition (Operator.arity o))
  o ₊ = Operator.posPost o

  -- Negative postconditions
  _₋ : (o : Operator) → List (Condition (Operator.arity o))
  o ₋ = Operator.negPost o

  -- All preconditions
  pres : (o : Operator) → List (Condition (Operator.arity o))
  pres o = (Operator.posPre o) ∪ᶜ (Operator.negPre o)

  -- All postconditions
  posts : (o : Operator) → List (Condition (Operator.arity o))
  posts o = (Operator.posPost o) ∪ᶜ (Operator.negPost o)

  {--
    Ground Operators are operators with all ground conditions.
  --}
  record GroundOperator : Set where
    field
      label : String
      posPre : List GroundCondition
      negPre : List GroundCondition
      posPost : List GroundCondition
      negPost : List GroundCondition

  {- Grounding an operator -}
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

    ground-Conditions : ∀ { s } → List (Condition s) → Vec TermConstant s → List GroundCondition
    ground-Conditions [] ts = []
    ground-Conditions (c ∷ cs) ts = ground-Condition c ts ∷ ground-Conditions cs ts

  -- ground : (o : Operator) → Vec TermConstant (Operator.arity o) → GroundOperator
  -- ground o ts = 
  --   let posPres = ground-Conditions (Operator.posPre o) ts
  --     in let negPres = ground-Conditions (Operator.negPre o) ts
  --       in let posPost = ground-Conditions (Operator.posPost o) ts
  --         in let negPosts = ground-Conditions (Operator.negPost o) ts
  --           in record { label = (Operator.label o) ; posPre = posPres ; negPre = negPres ; posPost = posPost ; negPost = negPosts }

  {- The Update Function -}
  -- update : GroundOperator → State → State
  -- update τ S = add (remove S (GroundOperator.negPost τ)) (GroundOperator.posPost τ)
  --   where
  --     add : State → List (Condition 0) → State
  --     add 𝕊 A = A ∪ᶜ 𝕊

  --     remove : State → List (Condition 0) → State
  --     remove [] R = [] 
  --     remove 𝕊 [] = 𝕊
  --     remove (s ∷ 𝕊) R with s ∈ᶜᵇ R
  --     ... | false = s ∷ remove 𝕊  R 
  --     ... | true = remove 𝕊 R  