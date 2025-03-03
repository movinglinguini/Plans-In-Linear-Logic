open import Data.Vec hiding (length)
open import Data.List hiding (merge)
open import Data.Nat using (_+_; z≤n)
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

  {- 
    Translation of operators into an unrestricted context.
    We prove that this part of the context is indeed unrestricted below.
  -}
  contextify-operators : (P : PlanProblem) → Context (2 + length (PlanProblem.terms P)) (length (PlanProblem.operators P))
  contextify-operators P = ⟨ (const "true") ∷ (const "false") ∷ translTs 0 z≤n (PlanProblem.terms P) , translOs (PlanProblem.operators P) ⟩

  {-
    Translation of state into a linear context.
    We prove that this part of the context is indeed linear below.
  -}
  contextify-state : (P : PlanProblem) → Context 0 (length (PlanProblem.conditions P)) 
  contextify-state P = ⟨ [] , translS (PlanProblem.initialState P) (PlanProblem.conditions P) ⟩

  {-
    Concatenates the operator and state contexts.
  -}
  contextOfProblem : (P : PlanProblem) 
                    → Context 
                        (2 + length (PlanProblem.terms P) + 0) 
                        ((length (PlanProblem.operators P)) + (length (PlanProblem.conditions P)))
  contextOfProblem P = contextify-operators P ++ᶜ contextify-state P

  {-
    The main translation function. Given a PlanProblem, output the translated context
    and translated goal as a proposition. We omit the mode of the goal context here. We
    will assume that it's linear in our proofs.
  -}
  translProb : ∀ (P : PlanProblem) 
              → (Context 
                    (2 + length (PlanProblem.terms P) + 0) 
                    ((length (PlanProblem.operators P)) + (length (PlanProblem.conditions P)))
                ) 
                  × Prop 
  translProb P = ⟨ (contextOfProblem P) , ⨂ (translG (PlanProblem.goals P)) ⟩

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