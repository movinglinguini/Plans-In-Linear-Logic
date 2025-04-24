open import Data.List hiding (_++_)
open import Data.Nat using (_+_; ℕ; _∸_)
open import Data.Fin using (toℕ)
open import Data.Vec hiding (length)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

open import Translations.Core.ConditionConfiguration
open import Translations.Core.PropAtom

open import Utils.BigTensor

module Translations.Core.Goal where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props PropAtom
  open import Logic.Core.Terms TermAtom
  open import Logic.Core.Modes

  {- 
    Goal translation. We turn each ground condition in the goal to an atomic
    proposition with true or false as its truth value depending on the boolean
    the condition was paired with.
  -}
  
  translG-Goals : (𝔾 : Goal) → Vec Prop (length 𝔾)
  translG-Goals 𝔾 = translConfig 𝔾

  translG : (P : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) → (Prop × Mode)
  translG (wf/prob _ _ _ _ 𝔾 _ _ _) = ⟨ (⨂ translG-Goals 𝔾) ⊗ ⊤ , Linear ⟩
      