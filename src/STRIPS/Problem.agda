open import Data.List hiding (head)
open import Data.Vec hiding (head)
open import Data.Vec.Bounded 
open import Data.Nat
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵛ_; _∉_ to _∉ᵛ_)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_; _∉_ to _∉ˡ_)
open import Data.List.Membership.Propositional.Properties
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable
open import Data.Maybe

module STRIPS.Problem where
  {- Repackaging the other parts of the STRIPS encoding -}
  open import STRIPS.Core.Common public
  open import STRIPS.Core.Sat public
  open import STRIPS.Core.Terms public
  open import STRIPS.Core.Conditions public
  open import STRIPS.Core.Operators public
  open import STRIPS.Core.Goals public
  open import STRIPS.Core.States public
  open import STRIPS.Core.Transitions public

  {- Definition of a planning problem -}
  variable
    n m q r : ℕ
    𝕋 : List TermConstant
    ℂ ℂ₁ ℂ₂ cs : List GroundCondition
    gs : List (GroundCondition × Bool)
    𝕔 : GroundCondition
    S S' : List GroundCondition
    𝕀 : State
    𝕆 : List Operator
    o : Operator
    𝔾 : Goal
    ts : Vec TermConstant (Operator.arity o)
    τ : Transition ℂ 𝕆

  {-
    Definition of a planning problem. A planning problem is a tuple
    〈 𝕋 , ℂ, 𝕀, 𝕆, 𝔾 ⟩ where

    1. 𝕋 is a vector of constant terms
    2. ℂ is a vector of ground conditions
    3. 𝕀 is a list subset of ℂ
    4. 𝕆 is a vector of operators
    5. 𝔾 is a goal definition
  -}
  data PlanProblem : List TermConstant → List GroundCondition → State → List Operator → Goal → Set where
    -- A well-formed planning problem is constituted of well-formed parts.
    -- We wrote the definition of 𝔾 to be well-formed.
    -- We add an argument for the well-formedness of the state 𝕀 as an argument.
    wf/prob : 
      (𝕋 : List TermConstant)
      (ℂ : List GroundCondition) (𝕀 : State)
      (𝕆 : List Operator) (𝔾 : Goal)
      (wf/conds : WfGroundConditions ℂ 𝕋)
      (wf/state : WfState 𝕀 ℂ)
      (wf/goal : WfState 𝔾 ℂ)
      → PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾

  private
    variable
      ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾

  stateOf : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 → List (GroundCondition × Bool)
  stateOf (wf/prob _ _ 𝕀 _ _ wf/conds wf/state wf/goal) = 𝕀

  -- open import Data.Vec.Membership.DecPropositional { A = GroundCondition } (_≟ᶜ_)
  -- maybeWfState : ∀ { n } → (S : List GroundCondition) → (ℂ : Vec GroundCondition n) → Maybe (State S ℂ)
  -- maybeWfState List.[] ℂ = just wf/state/z
  -- maybeWfState (c List.∷ S) ℂ with c ∈? ℂ
  -- ... | no ¬p = nothing
  -- ... | yes p₁ with maybeWfState S ℂ
  -- ...   | nothing = nothing
  -- ...   | just p₂ = just (wf/state/s p₂ p₁)
  -- {-
  --   Plan definitions

  --   From here, we define valid plans for planning problems. Plans are effectively
  --   lists of transitions that iteratively transform an initial state into one that
  --   satisfies the goal state.
  -- -}

  -- sat-τ wf/state/z τ = sat-τ-helper List.[] τ
  -- sat-τ (wf/state/s {c = c} {cs} inp x) τ = sat-τ-helper (c List.∷ cs) τ

  -- sat-τ? : (𝕊 : State S ℂ) → (τ : Transition ℂ 𝕆) → Dec (sat-τ 𝕊 τ)
  -- sat-τ? wf/state/z (wf/transition o ts x x₁) with sat? (Data.List.[]) (pres gτ)
  --   where
  --     ground[τ] : GroundOperator
  --     ground[τ] = ground o ts

  --     gτ : Operator
  --     gτ = toOperator ground[τ]
  -- ... | no ¬s = no (λ x₂ → ¬s x₂)
  -- ... | yes s = yes s 
  -- sat-τ? (wf/state/s {c = c} {cs} 𝕊 x) (wf/transition o ts x₁ x₂) with sat? (c Data.List.∷ cs) (pres gτ)
  --   where
  --     ground[τ] : GroundOperator
  --     ground[τ] = ground o ts

  --     gτ : Operator
  --     gτ = toOperator ground[τ]
  -- ... | no ¬s = no (λ x₂ → ¬s x₂)
  -- ... | yes s = yes s 

  -- -- We write inp ⟶[ τ ] out to mean that a transition τ can transform state inp into
  -- -- state out if inp satisfies the preconditions of ground(τ) and the conditions of
  -- -- inp are transformed into the conditions of out.
  data _⟶[_]_ : State → Transition ℂ 𝕆 → State → Set where
    wf/trans : ( inp : State) ( out : State)
      → sat-τ inp τ   →  (update S τ) ≡ S'
      ------------------------------------
      → inp ⟶[ τ ] out

  -- transition-from : (inp : State S ℂ) → (τ : Transition ℂ 𝕆) → Maybe (Σ (List GroundCondition) (λ S' → Σ (State S' ℂ) (λ out → inp ⟶[ τ ] out)))
  -- transition-from { S = S } inp τ with sat-τ? inp τ
  -- ... | no ¬t = nothing
  -- transition-from {S = S} {ℂ = ℂ} inp τ | yes t with wf-state? next-state ℂ 
  --   where
  --     next-state : List GroundCondition
  --     next-state = update S τ
  -- ... | nothing = nothing
  -- ... | just wf = just ⟨ update S τ , ⟨ wf , wf/trans inp wf t refl ⟩ ⟩
      

  -- Given an initial state and a goal, a well-formed plan is one that iteratively
  -- transforms the initial state into one that satisfies the goal.
  data Plan : State → Goal → Set where
    wf/plan/z : (S : State) (G : Goal)
      → sat S G
      → Plan S G

    wf/plan/s : (inp : State) (out : State) (τ : Transition ℂ 𝕆)
      (goal : Goal)
      → Plan out goal   →   inp ⟶[ τ ] out
      -------------------------------------
      → Plan inp goal

  -- -- Builds a plan from a list of transitions
  -- solver-plan : (S : State S ℂ) → (G : Goals gs ℂ) → List (Transition ℂ 𝕆) → Maybe (Plan S G)
  -- solver-plan {S} {gs = gs} 𝕊 𝔾 List.[] with sat? S gs
  -- ... | no ¬s = nothing
  -- ... | yes s = just (wf/plan/z 𝕊 𝔾 s)
  -- solver-plan {S} 𝕊 𝔾 (τ List.∷ τs) with transition-from 𝕊 τ
  -- ... | just ⟨ S' , ⟨ 𝕊' , trans ⟩ ⟩ with solver-plan 𝕊' 𝔾 τs
  -- ...   | just subplan = just (wf/plan/s 𝕊 𝕊' τ 𝔾 subplan trans)
  -- ...   | nothing = nothing
  -- solver-plan {S} 𝕊 𝔾 (τ List.∷ τs) | nothing = nothing

  -- -- Relation between plan problems and valid plans.
  data Solves : (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) → Plan 𝕀 𝔾 → Set where
    solves : (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) (plan : Plan 𝕀 𝔾)
      → Solves ℙ plan
    