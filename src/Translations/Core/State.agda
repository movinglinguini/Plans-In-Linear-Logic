open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Vec 
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵛ_)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_)
open import Data.Vec.Relation.Unary.Any
open import Data.List.Relation.Unary.Any

open import STRIPS.Problem hiding (Term)

open import Translations.Core.Condition
open import Translations.Core.PropAtom
open import Translations.Core.ConditionConfiguration

module Translations.Core.State where
  open import Logic.Core.Terms TermAtom
  
  open import Logic.Core.Props PropAtom
  open import Logic.Core.Modes
  open import Logic.Utils.ModeOf PropAtom

  private
    variable
      s : ℕ


  translS-Conditions : (𝕀 : State) → Vec (Prop × Mode) (Data.List.length 𝕀)
  translS-Conditions [] = []
  translS-Conditions (⟨ c , false ⟩ ∷ 𝕀) = ⟨ (` v[ (translC c) , (const "false") ]) , Linear ⟩ ∷ (translS-Conditions 𝕀)
  translS-Conditions (⟨ c , true ⟩ ∷ 𝕀) = ⟨ (` v[ (translC c) , (const "true") ]) , Linear ⟩ ∷ (translS-Conditions 𝕀)
  
  translS : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 → Vec (Prop × Mode) (Data.List.length 𝕀)
  translS (wf/prob _ _ 𝕀 _ _ _ _ _) = translS-Conditions 𝕀

  {- Some properties of translS -}

  -- If a condition config was in the state, then its translation is in the translation
  -- of the state.
  ∈-state⇒∈-transl : ∀ { s } 
    → ( prob : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 )
    → s ∈ˡ 𝕀 
    → ⟨ translConfig-Condition s , Linear ⟩ ∈ᵛ translS prob
  ∈-state⇒∈-transl {s = ⟨ fst , false ⟩} (wf/prob _ _ .(⟨ fst , false ⟩ ∷ _) _ _ wf/conds wf/state wf/goal) (here refl) = here refl
  ∈-state⇒∈-transl {s = ⟨ fst , true ⟩} (wf/prob _ _ .(⟨ fst , true ⟩ ∷ _) _ _ wf/conds wf/state wf/goal) (here refl) = here refl
  ∈-state⇒∈-transl {s = ⟨ fst , snd ⟩} (wf/prob _ _ .(⟨ fst₁ , false ⟩ ∷ xs) 𝕆 _ wf/conds (wf/state/s wf/state x) wf/goal) (there {⟨ fst₁ , false ⟩} {xs} mem) 
    = there (∈-state⇒∈-transl (wf/prob _ _ xs 𝕆 _ wf/conds wf/state wf/goal) mem)
  ∈-state⇒∈-transl {s = ⟨ fst , snd ⟩} (wf/prob _ _ .(⟨ fst₁ , true ⟩ ∷ xs) 𝕆 _ wf/conds (wf/state/s wf/state x) wf/goal) (there {⟨ fst₁ , true ⟩} {xs} mem) 
    = there (∈-state⇒∈-transl (wf/prob _ _ xs 𝕆 _ wf/conds wf/state wf/goal) mem)
