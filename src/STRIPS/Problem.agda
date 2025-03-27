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
    𝕋 : Vec TermConstant n
    ℂ ℂ₁ ℂ₂ cs : Vec GroundCondition m
    gs : List (GroundCondition × Bool)
    𝕔 : GroundCondition
    𝕀 S S' : List GroundCondition
    𝕆 : Vec Operator r
    o : Operator
    𝔾 : Goals gs ℂ
    ts : Vec TermConstant (Operator.arity o)
    τ : Transition o ts ℂ 𝕆

  {-
    Definition of a planning problem. A planning problem is a tuple
    〈 ℂ, 𝕀, 𝕆, 𝔾 ⟩ where

    1. ℂ is a vector of ground conditions
    2. 𝕀 is a list subset of ℂ
    3. 𝕆 is a vector of operators
    4. 𝔾 is a goal definition
  -}
  data PlanProblem : ∀ { gs }
    → (ℂ : Vec GroundCondition n) -- The list of legal ground conditions that can be used.
    → List GroundCondition  -- The initial state
    → Vec Operator m  -- The list of legal operators.
    → Goals gs ℂ  -- The goal definition
    → Set
    where
    -- A well-formed planning problem is constituted of well-formed parts.
    -- We wrote the definition of 𝔾 to be well-formed.
    -- We add an argument for the well-formedness of the state 𝕀 as an argument.
    wf/prob : 
      (ℂ : Vec GroundCondition n) (𝕀 : List GroundCondition)
      (𝕆 : Vec Operator m) (𝔾 : Goals gs ℂ)
      (wf/state : State 𝕀 ℂ)
      → PlanProblem ℂ 𝕀 𝕆 𝔾

  private
    variable
      ℙ : PlanProblem ℂ 𝕀 𝕆 𝔾

  initialState : PlanProblem ℂ 𝕀 𝕆 𝔾 → State 𝕀 ℂ
  initialState (wf/prob _ _ _ _ wf/state) = wf/state

  open import Data.Vec.Membership.DecPropositional { A = GroundCondition } (_≟ᶜ_)
  maybeWfState : ∀ { n } → (S : List GroundCondition) → (ℂ : Vec GroundCondition n) → Maybe (State S ℂ)
  maybeWfState List.[] ℂ = just wf/state/z
  maybeWfState (c List.∷ S) ℂ with c ∈? ℂ
  ... | no ¬p = nothing
  ... | yes p₁ with maybeWfState S ℂ
  ...   | nothing = nothing
  ...   | just p₂ = just (wf/state/s p₂ p₁)
  {-
    Plan definitions

    From here, we define valid plans for planning problems. Plans are effectively
    lists of transitions that iteratively transform an initial state into one that
    satisfies the goal state.
  -}

  -- Alias for satisfying a transition's ground operator since we have to go through 
  -- a few definitions to do it.
  private
    sat-τ-helper : ∀ { o ts } →  List GroundCondition → Transition o ts ℂ 𝕆 → Set
    sat-τ-helper S (wf/transition o ts _ _) = sat S (pres gτ)
      where
        ground[τ] : GroundOperator
        ground[τ] = ground o ts

        gτ : Operator
        gτ = toOperator ground[τ]

  -- We say a state S satisfies a transition τ if
  -- the conditions of S satisfy the preconditions of ground(τ).
  sat-τ : ∀ { o ts } → State S ℂ → Transition o ts ℂ 𝕆 → Set
  sat-τ wf/state/z τ = sat-τ-helper List.[] τ
  sat-τ (wf/state/s {c = c} {cs} inp x) τ = sat-τ-helper (c List.∷ cs) τ

  -- We write inp ⟶[ τ ] out to mean that a transition τ can transform state inp into
  -- state out if inp satisfies the preconditions of ground(τ) and the conditions of
  -- inp are transformed into the conditions of out.
  data _⟶[_]_ : ∀ { o ts } → State S ℂ → Transition o ts ℂ 𝕆 → State S' ℂ → Set where
    wf/trans : ( inp : State S ℂ) ( out : State S' ℂ )
      → sat-τ inp τ   →  (update S τ) ≡ S'
      ------------------------------------
      → inp ⟶[ τ ] out


  -- Given an initial state and a goal, a well-formed plan is one that iteratively
  -- transforms the initial state into one that satisfies the goal.
  data Plan : State S ℂ → Goals gs ℂ → Set where
    wf/plan/z : (state : State S ℂ) (goal : Goals gs ℂ)
      → sat S gs
      → Plan state goal

    wf/plan/s : (inp : State S ℂ) (out : State S' ℂ) (τ : Transition o ts ℂ 𝕆)
      (goal : Goals gs ℂ)
      → Plan out goal   →   inp ⟶[ τ ] out
      -------------------------------------
      → Plan inp goal


  -- Relation between plan problems and valid plans.
  data Solves : (ℙ : PlanProblem ℂ 𝕀 𝕆 𝔾) → Plan (initialState ℙ) 𝔾 → Set where
    solves : (ℙ : PlanProblem ℂ 𝕀 𝕆 𝔾) (plan : Plan (initialState ℙ) 𝔾)
      → Solves ℙ plan
    

  -- -- A plan is a list of ground operators
  -- Plan = List GroundOperator

  -- -- Some syntactic sugar for satisfaction that we're going to use
  -- satGoals : State → Goals ℂ gs → Set
  -- satGoals S wf/goal/z = sat-Conditions S []
  -- satGoals S (wf/goal/s {gs = gs} 𝔾 wfcond) = sat-Conditions S gs

  -- satOp : State → GroundOperator → Set
  -- satOp S τ = sat S ⟨ GroundOperator.posPre τ , GroundOperator.negPre τ ⟩

  -- satOp? : (S : State) → (τ : GroundOperator) → Dec (satOp S τ)
  -- satOp? S τ = sat? S ⟨ GroundOperator.posPre τ , GroundOperator.negPre τ ⟩

  -- {- Relation between an input state and output state of a transition. -}
  -- data _⟶[_]_ : State → GroundOperator → State → Set where
  --   transition : ∀ { S S' τ }
  --     → satOp S τ     →   S' ≡ (update τ S)
  --     --------------------------------------
  --     → S ⟶[ τ ] S'  

  -- {-
  --   Now we can finally define a well-formed plan. This is a doozy.
  --   In general, a well-formed plan is one where
  --   1. for every transition τ in the plan, there exists a ground operator o and list of well-formed constant terms ts
  --     where if we ground o with ts, we get τ.
  --   2. every result of an update using τ yields a well-formed state (a.k.a., the update is well-formed)
  --   3. the plan results in a state that satisfies the goal state.
  -- -}
  -- data WfPlan : (PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) → Plan → Set where
  --   -- If we're here, then we just need to show that the plan state 𝕀 satisfies the goal 𝔾
  --   wf/plan/z :
  --     satGoals 𝕀 𝔾
  --     -----------------------
  --     → WfPlan (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾) []

  --   -- If we're here, we need to show that our transition τ is well-formed (a.k.a., can be constructed
  --   -- by grounding a problem operator. We then recurse on the updated state.
  --   wf/plan/s : ∀ { P 𝕀' }
  --     → WfPlan (wf/prob 𝕋 ℂ 𝕀' 𝕆 𝔾) P
  --     → 𝕀 ⟶[ τ ] 𝕀'
  --     -- → Σ Operator (λ  → o ∈ˡ 𝕆 → Σ (Vec TermConstant (Operator.arity o)) λ ts → τ ≡ ground o ts)
  --     → WfPlan (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾) (τ ∷ P)
  
  -- -- Writing a simple solver
  -- -- solver : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 ) → ( P : Plan ) → Maybe (WfPlan ℙ )
  -- -- solver (wf/prob _ _ 𝕀 _ 𝔾) [] with satGoal? 𝕀 𝔾
  -- -- ... | no ¬p = nothing
  -- -- ... | yes p = just (wf/plan/z p) 
  -- -- solver (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾) (τ ∷ P) with satOp? 𝕀 τ
  -- -- ... | no ¬p = nothing
  -- -- ... | yes p with solver (wf/prob 𝕋 ℂ (update τ 𝕀) 𝕆 𝔾) P
  -- -- ... | nothing = nothing
  -- -- ... | just x = just (wf/plan/s x (transition p refl))
  