open import Data.List hiding (_++_)
open import Data.Nat using (_+_; ℕ; _∸_)
open import Data.Fin using (toℕ)
open import Data.Vec hiding (length)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module Translations.Core.Goal where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props PropAtom
  open import Logic.Core.Terms TermAtom

  {- 
    Goal translation. We turn each ground condition in the goal to an atomic
    proposition with true or false as its truth value depending on the boolean
    the condition was paired with.
  -}

  translG-Goal : (GroundCondition × Bool) → Prop
  translG-Goal ⟨ c , false ⟩ = ` v[ translC c , const "false" ]
  translG-Goal ⟨ c , true ⟩ = ` v[ translC c , const "true" ]
  
  translG-Goals : ∀ (G : Goal) → Vec Prop (length G)
  translG-Goals [] = []
  translG-Goals (g ∷ G) = (translG-Goal g) ∷ translG-Goals G

  translG : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } (P : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) → Vec Prop (length 𝔾)
  translG (wf/prob _ _ _ _ 𝔾 _) = translG-Goals 𝔾
   