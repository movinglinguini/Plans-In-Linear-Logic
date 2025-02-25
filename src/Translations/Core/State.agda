open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Vec hiding (length)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Data.Vec.Membership.Propositional 
open import Data.Vec.Relation.Unary.Any

module Translations.Core.State where
  open import Translations.Core.Condition
  open import STRIPS.Problem hiding (Term)
  open import Logic.Core.Terms TermAtom
  
  infix 10 v[_,_]
  data Proposition : Set where
    v[_,_] : TCondition → Term → Proposition

  open import Logic.Core.Props Proposition
  open import Logic.Core.Modes
  open import Logic.Utils.ModeOf Proposition

  private
    variable
      𝕊 ℙ : List Condition

    translS-helper : Condition → Bool → Prop
    translS-helper c false = ` v[ (translC c) , term "false" ]
    translS-helper c true = ` v[ (translC c) , term "true" ]

  translS : (𝕊 ℙ : List Condition) → Vec (Prop × Mode) (length ℙ) -- Vec Proposition (length ℙ)
  translS 𝕊 [] = []
  translS 𝕊 (x ∷ ℙ) = ⟨ translS-helper x (x ∈ᶜᵇ 𝕊) , Linear ⟩ ∷ translS 𝕊 ℙ

  private
    translS-pos : ∀ { P s } → WfProblem P → s ∈ (fromList (PlanProblem.initialState P)) → ⟨ ` v[ translC s , term "true" ] , Linear ⟩ ∈ (translS (PlanProblem.initialState P) (PlanProblem.conditions P)) 
    translS-pos {P} WfP mem with PlanProblem.initialState P | PlanProblem.conditions P | translS (PlanProblem.initialState P) (PlanProblem.conditions P)
    ... | x ∷ a | [] | c = {!   !}
    ... | x ∷ a | x₁ ∷ b | c = {!   !}

  translS-sat-pos : ∀ { 𝕘 } { P : PlanProblem } 
    → WfProblem P
    → sat (PlanProblem.initialState P) ⟨ Goal.pos (PlanProblem.goals P) , Goal.neg (PlanProblem.goals P) ⟩
    → 𝕘 ∈ (fromList (Goal.pos (PlanProblem.goals P)))
    → ⟨ ` v[ translC 𝕘 , term "true" ] , Linear ⟩ ∈ (translS (PlanProblem.initialState P) (PlanProblem.conditions P))
  translS-sat-pos {𝕊} {P = P} ⟨ fst₁ , ⟨ fst₂ , ⟨ fst , snd ⟩ ⟩ ⟩ sat mem with (PlanProblem.goals P) | (PlanProblem.conditions P)
  ... | a | b = {!   !}

