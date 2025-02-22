open import Data.Vec hiding (length)
open import Data.List 
open import Data.Nat using (_+_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Translations.Translations where
  {- Repackage other pieces of the translation -}
  open import Translations.Core.Term public
  open import Translations.Core.Condition public
  open import Translations.Core.State public
  open import Translations.Core.Goal public
  open import Translations.Core.Operator public
  open import Translations.Core.Contextify public
  
  open import STRIPS.Problem
  open import ADJ.Core

  -- The problem translation function
  contextify-operators : (P : PlanProblem) → Context (length (PlanProblem.terms P)) (length (PlanProblem.operators P))
  contextify-operators P = ⟨ translTs (PlanProblem.terms P) , translOs (PlanProblem.operators P) ⟩

  contextify-state : (P : PlanProblem) → Context 0 (length (PlanProblem.conditions P)) 
  contextify-state P = ⟨ [] , translS (PlanProblem.initialState P) (PlanProblem.conditions P) ⟩

  contextOfProblem : (P : PlanProblem) → Context (length (PlanProblem.terms P) + 0) ((length (PlanProblem.operators P)) + (length (PlanProblem.conditions P)))
  contextOfProblem P = contextify-operators P ++ᶜ contextify-state P

  translProb : ∀ (P : PlanProblem) → Set 
  translProb P = (contextify-operators P ++ᶜ contextify-state P) ⊢ⁱ translG (PlanProblem.goals P)
 