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
  open import STRIPS.Core.Sat public
  open import STRIPS.Core.Terms public
  open import STRIPS.Core.Conditions public
  open import STRIPS.Core.Operators public
  open import STRIPS.Core.Goals public
  open import STRIPS.Core.Transitions public

  {- Definition of a planning problem -}
  variable
    n m x : ℕ
    𝕋 : Vec TermConstant x
    ℂ ℂ₁ ℂ₂ cs : Vec GroundCondition n
    gs : List (GroundCondition × Bool)
    𝕔 : GroundCondition
    𝕀 : Vec GroundCondition n
    𝕆 : Vec Operator m
    𝕠 : Operator
    τ : GroundOperator
    𝔾 : Goals ℂ gs

  -- {-
  --  A well-formed plan problem is one where:
  --  1. 
  -- -}
  -- data PlanProblem : ∀ { gs n m x }
  --   → Vec TermConstant x 
  --   → ( ℂ : Vec GroundCondition n )
  --   → State 
  --   → Vec Operator m
  --   → Goals ℂ gs
  --   → Set where
  --   wf/prob : ∀ { n m x gs } 
  --     (𝕋 : Vec TermConstant x) (ℂ : Vec GroundCondition n) (𝕀 : State) 
  --     (𝕆 : Vec Operator m) (𝔾 : Goals ℂ gs)
  --     → PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾

  -- private
  --   variable
  --     ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾

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
 