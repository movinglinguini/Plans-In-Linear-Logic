open import Data.List hiding (head)
open import Data.Vec hiding (head)
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
  open import STRIPS.Core.Terms public
  open import STRIPS.Core.Conditions public
  open import STRIPS.Core.Operators public
  open import STRIPS.Core.Goals public
  -- open import STRIPS.Core.Plans public

  {- 
    A PlanProblem is defined as a tuple ⟨ 𝕋 , ℂ , 𝕀 , 𝕆 , 𝔾 ⟩, where
      - 𝕋 is a set of terms
      - ℂ is a set of conditions
      - 𝕀 is the problem's state
      - 𝕆 is a set of operators
      - 𝔾 is the goal tuple

    This module defines a well-formed problem, which takes quite a bit of
    setup to formulate.
  -}
  private
    variable
      𝕋 : List TermConstant
      ℂ ℂ₁ ℂ₂ : List GroundCondition
      𝕔 : GroundCondition
      𝕀 : State
      𝕆 : List Operator
      𝕠 : Operator
      τ : GroundOperator
      𝔾 : Goal

  {-
    A list of ground conditions is well-formed if:
    1. each element can be found in the problem condition list (ℂ)
  -}
  data WfGroundConditions : List GroundCondition → List GroundCondition → Set where
    wf/gconds : 
      (∀ c → c ∈ˡ ℂ₁ → c ∈ˡ ℂ₂)
      →  WfGroundConditions ℂ₁ ℂ₂

  {-
    A list of conditions is well-formed if all conditions are well-formed. A condition
    is well-formed if all its constant terms can be found in the problem term list (𝕋).
  -}
  data WfConditions : ∀ { s } → List (Condition s) → List TermConstant → Set where
    wf/conds : ∀ { s } { C : List (Condition s) }
      → (∀ c t  → c ∈ˡ C → t ∈ˡ (constantsOf c) → t ∈ˡ 𝕋)
      → WfConditions C 𝕋

  {-
    An operator is well-formed if all of its conditions are well-formed.
  -}
  data WfOperator : Operator → List TermConstant → Set where 
    wf/op : ∀ { o } 
      → WfConditions (o ⁺) 𝕋
      → WfConditions (o ⁻) 𝕋
      → WfConditions (o ₊) 𝕋
      → WfConditions (o ₋) 𝕋
      → WfOperator o 𝕋

  {-
    A list of operators is well-formed if all its elements are well-formed.
  -}
  data WfOperators : List Operator → List TermConstant → Set where
    wf/ops : 
      (∀ { o } → o ∈ˡ 𝕆 → WfOperator o 𝕋)
      → WfOperators 𝕆 𝕋

  {-
    A well-formed goal is one where:
    1. all positive and negative conditions are well-formed with respect to the
      plan problem's condition and term lists
    2. the positive and negative term lists are disjoint.
  -}
  data WfGoal : Goal → List GroundCondition → Set where
    wf/goal : 
      WfGroundConditions (getConditions-Goal 𝔾) ℂ
      -- → (∀ { g } → g ∈ˡ (getPositives-Goal 𝔾) → g ∉ˡ (getNegatives-Goal 𝔾))
      → WfGoal 𝔾 ℂ

  {-
   A well-formed plan problem is one where:
   1. 
  -}
  data PlanProblem :
    List TermConstant 
    → List GroundCondition 
    → State 
    → List Operator
    → Goal
    → Set where
    wf/prob : ∀ (𝕋 : List TermConstant) (ℂ : List GroundCondition) (𝕀 : State) 
      (𝕆 : List Operator) (𝔾 : Goal)
      → PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾

  private
    variable
      ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾
      wfconds : WfConditions ℂ 𝕋
      wfstate : WfGroundConditions 𝕀 ℂ
      wfops : WfOperators 𝕆 𝕋
      wfgoal : WfGoal 𝔾 ℂ

  {--------------
    Properties of Well-formed Problems
  ---------------}

  {- If you have a well-formed goal, shortening the goal is still well-formed. -}
  -- wfProb-smaller-goal-lemma : ∀ { ℂ 𝔾 𝕘 } → WfGoal (𝕘 ∷ 𝔾) ℂ → WfGoal 𝔾 ℂ
  -- wfProb-smaller-goal-lemma (wf/goal (wf/gconds wf-goal-conds)) 
  --   = wf/goal (wf/gconds (λ x → wf-goal-conds (there x))) 

  -- wfProb-smaller-goal : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 𝕘 } → PlanProblem 𝕋 ℂ 𝕀 𝕆 (𝕘 ∷ 𝔾) → PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾
  -- wfProb-smaller-goal (wf/prob 𝕋 ℂ 𝕀 𝕆 (_ ∷ 𝔾) x x₁ x₂ (wf/goal (wf/gconds wf-goal-conds))) 
  --   = wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾 x x₁ x₂ (wf/goal (wf/gconds (λ x₃ → wf-goal-conds (there x₃))))

  {-
    Now, we talk about well-formed plans, or solutions to plan-problems.
    First of all, a plan is just a list of ground conditions, but with a caveat.
    Each ground condition needs to be a grounding of an operator from the original
    problem, using terms from the plan problem.
  -}
  data WfGroundOperator : GroundOperator → (o : Operator) → Vec TermConstant (Operator.arity o) → List TermConstant → Set where
    wf/groundop : ∀ { o } { ts : Vec TermConstant (Operator.arity o) }
      → (∀ { t } → t ∈ᵛ ts → t ∈ˡ 𝕋)
      → τ ≡ ground o ts
      → WfGroundOperator τ o ts 𝕋

  -- A plan is a list of ground operators
  Plan = List GroundOperator

  -- Some syntactic sugar for satisfaction that we're going to use
  satGoal : State → Goal → Set
  satGoal S G = sat S ⟨ getPositives-Goal G , getNegatives-Goal G ⟩

  satGoal′ : State → Goal → Set
  satGoal′ S G = sat′ S ⟨ getPositives-Goal G , getNegatives-Goal G ⟩

  satGoal? : (S : State) → (G : Goal) → Dec (satGoal S G)
  satGoal? S G = sat? S ⟨ getPositives-Goal G , getNegatives-Goal G ⟩

  {- Properties of satGoal -}
  ∈-xs⇒∈-x∷xs : ∀ { v x xs } → v ∈ˡ xs → v ∈ˡ (x ∷ xs)
  ∈-xs⇒∈-x∷xs mem = there mem

  satGoal⇒smaller-satGoal : ∀ { g G S } → satGoal′ S (g ∷ G) → satGoal′ S G
  satGoal⇒smaller-satGoal {G = G} ⟨ fst , snd ⟩ with getPositives-Goal G | getNegatives-Goal G
  ... | [] | [] = ⟨ (λ g x → fst g {! x  !}) , {!   !} ⟩
  ... | [] | x ∷ b = {!   !}
  ... | x ∷ a | [] = {!   !}
  ... | x ∷ a | x₁ ∷ b = {!   !}  -- ⟨ (λ g₁ x → fst g₁ {! ∈-xs⇒∈-x∷xs  !}) , {!   !} ⟩
  
  satOp : State → GroundOperator → Set
  satOp S τ = sat S ⟨ GroundOperator.posPre τ , GroundOperator.negPre τ ⟩

  satOp? : (S : State) → (τ : GroundOperator) → Dec (satOp S τ)
  satOp? S τ = sat? S ⟨ GroundOperator.posPre τ , GroundOperator.negPre τ ⟩

  {- Relation between an input state and output state of a transition. -}
  data _⟶[_]_ : State → GroundOperator → State → Set where
    transition : ∀ { S S' τ }
      → satOp S τ     →   S' ≡ (update τ S)
      --------------------------------------
      → S ⟶[ τ ] S'  

  {-
    Now we can finally define a well-formed plan. This is a doozy.
    In general, a well-formed plan is one where
    1. for every transition τ in the plan, there exists a ground operator o and list of well-formed constant terms ts
      where if we ground o with ts, we get τ.
    2. every result of an update using τ yields a well-formed state (a.k.a., the update is well-formed)
    3. the plan results in a state that satisfies the goal state.
  -}
  data WfPlan : (PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) → Plan → Set where
    -- If we're here, then we just need to show that the plan state 𝕀 satisfies the goal 𝔾
    wf/plan/z : 
      satGoal 𝕀 𝔾
      → WfPlan (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾) []

    -- If we're here, we need to show that our transition τ is well-formed (a.k.a., can be constructed
    -- by grounding a problem operator. We then recurse on the updated state.
    wf/plan/s : ∀ { P 𝕀' }
      → WfPlan (wf/prob 𝕋 ℂ 𝕀' 𝕆 𝔾) P
      → 𝕀 ⟶[ τ ] 𝕀'
      -- → Σ Operator (λ  → o ∈ˡ 𝕆 → Σ (Vec TermConstant (Operator.arity o)) λ ts → τ ≡ ground o ts)
      → WfPlan (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾) (τ ∷ P)
  
  -- Writing a simple solver
  solver : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } → ( ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 ) → ( P : Plan ) → Maybe (WfPlan ℙ P)
  solver (wf/prob _ _ 𝕀 _ 𝔾) [] with satGoal? 𝕀 𝔾
  ... | no ¬p = nothing
  ... | yes p = just (wf/plan/z p) 
  solver (wf/prob 𝕋 ℂ 𝕀 𝕆 𝔾) (τ ∷ P) with satOp? 𝕀 τ
  ... | no ¬p = nothing
  ... | yes p with solver (wf/prob 𝕋 ℂ (update τ 𝕀) 𝕆 𝔾) P
  ... | nothing = nothing
  ... | just x = just (wf/plan/s x (transition p refl))
