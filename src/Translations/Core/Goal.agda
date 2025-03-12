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

  -- Translate the positives and then the negatives, and then combine.
  translG-Goals : ∀ (G : Goal) → Vec Prop (length G)
  translG-Goals [] = []
  translG-Goals (⟨ fst , false ⟩ ∷ G) = ` v[ translC fst , const "false" ] ∷ translG-Goals G
  translG-Goals (⟨ fst , true ⟩ ∷ G) = ` v[ translC fst , const "true" ] ∷ translG-Goals G

  translG : ∀ { 𝕋 ℂ 𝕀 𝕆 𝔾 } (P : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) → Vec Prop (length 𝔾)
  translG (wf/prob _ _ _ _ 𝔾) = translG-Goals 𝔾
   