open import Data.Vec hiding (length)
open import Data.List hiding (merge)
open import Data.Nat using (_+_; z≤n; ℕ)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality


module Translations.Translations where
  {- Repackage other pieces of the translation -}
  open import Translations.Core.Term public
  open import Translations.Core.Condition public
  open import Translations.Core.State public
  open import Translations.Core.Goal public
  open import Translations.Core.Operator public
  
  open import STRIPS.Problem
  open import ADJ.Core

  open import Utils.AllOfMode
  open import Utils.BigTensor

  {-
    Here, we define the problem translation function in pieces.
  -}

  -- Some helper functions/syntactic sugar

  -- Expected length of the term context, which will consist of
  -- all translated terms of P plus "true" and "false"
  lenTermCtxt : PlanProblem → ℕ
  lenTermCtxt P = 2 + length (PlanProblem.terms P)

  -- Expected length of the unrestricted context, which will
  -- consist of all translated operators of P
  lenUnrCtxt : PlanProblem → ℕ
  lenUnrCtxt P = length (PlanProblem.operators P)

  -- Expected length of the linear context, which will
  -- consist of all translated conditions of P
  lenLinCtxt : PlanProblem → ℕ
  lenLinCtxt P = length (PlanProblem.conditions P)

  -- The expected size of the context of the sequent
  -- obtained from translating a problem is the size of
  -- the term context (plus 0) and the combined length of
  -- the unrestricted and linear contexts. We need the plus 0
  -- because we are going to get the translated context through
  -- concatenation.
  CtxtP : PlanProblem → Set
  CtxtP P = Context ((lenTermCtxt P) + 0) ((lenUnrCtxt P) + (lenLinCtxt P))

  {- 
    Translation of operators into an unrestricted context.
    We prove that this part of the context is indeed unrestricted below.
  -}
  contextify-operators : (P : PlanProblem) → Context (lenTermCtxt P) (lenUnrCtxt P)
  contextify-operators P 
    = ⟨ (const "true") ∷ (const "false") ∷ translTs 0 z≤n (PlanProblem.terms P) , translOs (PlanProblem.operators P) ⟩

  {-
    Translation of state into a linear context.
    We prove that this part of the context is indeed linear below.
  -}
  contextify-state : (P : PlanProblem) → Context 0 (lenLinCtxt P) 
  contextify-state P = ⟨ [] , translS (PlanProblem.initialState P) (PlanProblem.conditions P) ⟩

  {-
    Concatenates the operator and state contexts.
  -}
  contextOfProblem : (P : PlanProblem) → CtxtP P
  contextOfProblem P = contextify-operators P ++ᶜ contextify-state P

  {-
    The main translation function. Given a PlanProblem, output the translated context
    and translated goal as a proposition. We omit the mode of the goal context here. We
    will assume that it's linear in our proofs.
  -}
  translProb : ∀ (P : PlanProblem) → (CtxtP P) × Prop 
  translProb P = ⟨ (contextOfProblem P) , (⨂ (translG (PlanProblem.goals P))) ⊗ ⊤ ⟩

  {------
  - Properties of translations
  ------}

  {- Properties of problem translation -}

  -- The state translation is fully linear
  context-state-all-lin : ∀ { P } → AllOfMode Linear (contextify-state P)
  context-state-all-lin {record { terms = terms ; conditions = [] ; initialState = initialState ; operators = operators ; goals = goals }} = all-mode/z
  context-state-all-lin {record { terms = terms ; conditions = x ∷ conditions ; initialState = initialState ; operators = operators ; goals = goals }} 
    = all-mode/s (context-state-all-lin { P = record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = goals } }) refl

  -- The operator translation is fully unrestricted
  context-operator-all-unr : ∀ { P } → AllOfMode Unrestricted (contextify-operators P)
  context-operator-all-unr {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = [] ; goals = goals }} = all-mode/z
  context-operator-all-unr {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = x ∷ operators ; goals = goals }} 
    = all-mode/s (context-operator-all-unr { record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = goals } }) refl

  -- The operator context is weakenable
  context-operator-cWeak : ∀ { P } → cWeakenable (contextify-operators P)
  context-operator-cWeak {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = [] ; goals = goals }} = weak/n
  context-operator-cWeak {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = x ∷ operators ; goals = goals }} 
    = weak/c (context-operator-cWeak {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = goals }}) mweak/u
  
  -- The operator context is contractable
  context-operator-cContr : ∀ { P } → cContractable (contextify-operators P)
  context-operator-cContr {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = [] ; goals = goals }} = cont/n
  context-operator-cContr {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = x ∷ operators ; goals = goals }} 
    = cont/c (context-operator-cContr {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = operators ; goals = goals }}) mcontract/u

  -- The operator context can merge with itself
  context-operator-merge : ∀ { P Γ } → Γ ≡ (contextify-operators P) → merge Γ Γ Γ
  context-operator-merge {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = [] ; goals = goals }} {Γ = .(contextify-operators (record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = [] ; goals = goals }))} refl = mg/n
  context-operator-merge {record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = x ∷ operators ; goals = goals }} {Γ = .(contextify-operators (record { terms = terms ; conditions = conditions ; initialState = initialState ; operators = x ∷ operators ; goals = goals }))} refl 
    = mg/c (context-operator-merge
       {record
        { terms = terms
        ; conditions = conditions
        ; initialState = initialState
        ; operators = operators
        ; goals = goals
        }}
       refl) u∙u