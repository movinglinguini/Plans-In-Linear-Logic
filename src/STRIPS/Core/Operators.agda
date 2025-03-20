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

module STRIPS.Core.Operators where
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Terms
  
  -- An operator comes with its own scope and arity
  record Operator : Set where
    field
      label : String
      arity : ℕ
      preconditions : List ((Condition arity) × Bool)
      postconditions : List ((Condition arity) × Bool)

  -- WIP : Better definitions for operators and ground operators
  data Operators : Set where
    wf/operator : ∀ ( arity : ℕ ) 
      → (preconds : List ((Condition arity) × Bool))
      → (postconds : List ((Condition arity) × Bool)) 
      → Operators

  -- A ground operator is well-formed if all of its conditions can be found in the problem conditions
  data GroundOperators : ∀ { n } → List (GroundCondition × Bool) → List (GroundCondition × Bool) → Vec GroundCondition n → Set where
    wf/groundoperator/z : ∀ { n } → { ℂ : Vec GroundCondition n } → GroundOperators [] [] ℂ
    wf/groundoperator/pres/s : ∀ { n } { p pres posts } { ℂ : Vec GroundCondition n }
      → GroundOperators pres posts ℂ → (proj₁ p ∈ ℂ)
      ---------------------------------------------
      → GroundOperators (p ∷ pres) posts ℂ
    wf/groundoperator/posts/s : ∀ { n } { p pres posts } { ℂ : Vec GroundCondition n }
      → GroundOperators pres posts ℂ → (proj₁ p) ∈ ℂ
      ----------------------------
      → GroundOperators pres (p ∷ posts) ℂ

  {- Some syntactic sugar for extracting parts of operators -}
  infix 50 _⁺ _⁻ _₊ _₋

  private
    get-Positives : ∀ { s } → List ((Condition s) × Bool) → List (Condition s)
    get-Positives [] = []
    get-Positives ((fst , false) ∷ xs) = get-Positives xs
    get-Positives ((fst , true) ∷ xs) = fst ∷ get-Positives xs

    get-Negatives : ∀ { s } → List ((Condition s) × Bool) → List (Condition s)
    get-Negatives [] = []
    get-Negatives ((fst , false) ∷ xs) = fst ∷ get-Negatives xs
    get-Negatives ((fst , true) ∷ xs) = get-Negatives xs

  -- Positive preconditions
  _⁺ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁺ = get-Positives (Operator.preconditions o)

  -- Negative preconditions
  _⁻ : (o : Operator) → List (Condition (Operator.arity o))
  o ⁻ = get-Negatives (Operator.preconditions o)

  -- Positive postconditions
  _₊ : (o : Operator) → List (Condition (Operator.arity o))
  o ₊ = get-Positives (Operator.postconditions o)

  -- Negative postconditions
  _₋ : (o : Operator) → List (Condition (Operator.arity o))
  o ₋ = get-Negatives (Operator.postconditions o)

  -- All preconditions
  pres : (o : Operator) → List (Condition (Operator.arity o))
  pres o = o ⁺ ∪ᶜ o ⁻ -- (Operator.posPre o) ∪ᶜ (Operator.negPre o)

  -- All postconditions
  posts : (o : Operator) → List (Condition (Operator.arity o))
  posts o = o ₊ ∪ᶜ o ₋ -- (Operator.posPost o) ∪ᶜ (Operator.negPost o)

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

  ground : (o : Operator) → Vec TermConstant (Operator.arity o) → GroundOperator
  ground o ts = 
    let posPres = ground-Conditions (o ⁺) ts
      in let negPres = ground-Conditions (o ⁻) ts
        in let posPost = ground-Conditions (o ₊) ts
          in let negPosts = ground-Conditions (o ₋) ts
            in record { label = (Operator.label o) ; posPre = posPres ; negPre = negPres ; posPost = posPost ; negPost = negPosts }

  {- The Update Function -}
  update : GroundOperator → State → State
  update τ S = add (remove S (GroundOperator.negPost τ)) (GroundOperator.posPost τ)
    where
      add : State → List (Condition 0) → State
      add 𝕊 A = A ∪ᶜ 𝕊

      remove : State → List (Condition 0) → State
      remove [] R = [] 
      remove 𝕊 [] = 𝕊
      remove (s ∷ 𝕊) R with s ∈ᶜᵇ R
      ... | false = s ∷ remove 𝕊  R 
      ... | true = remove 𝕊 R    