open import Data.Nat
open import Data.List hiding (length)
open import Data.Bool
open import Data.Vec 
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵛ_) 
open import Data.Vec.Relation.Unary.Any
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_; _∉_ to _∉ˡ_)
open import Data.List.Relation.Unary.Any

module Translations.Core.State where
  open import Translations.Core.Condition
  open import STRIPS.Problem hiding (Term)
  open import Logic.Core.Terms TermAtom

  open import Data.List.Membership.DecPropositional { A = GroundCondition } (_≟ᶜ_)
  
  -- We are ultimately translating Conditions into PropAtoms,
  -- which contain translated conditions (TCondition) + a truth value term.
  infix 10 v[_,_]
  data PropAtom : Set where
    v[_,_] : ∀ { s } → TCondition s → Term s → PropAtom

  open import Logic.Core.Props PropAtom
  open import Logic.Core.Modes
  open import Logic.Utils.ModeOf PropAtom

  private
    variable
      s : ℕ
      𝕊 ℙ : List (Condition s)

  -- Helper function for translS
  -- Bool is supposed to represent whether or not the condition c was in the state we
  -- are translating over. If it is, then the PropAtom we translate to gets a truth
  -- value of "true". Otherwise, it gets "false".
  translS-Condition : ∀ { S } ( c : GroundCondition ) → Dec (c ∈ S) → PropAtom
  translS-Condition c (false because _) = v[ (translC c) , const "false" ]
  translS-Condition c (true because _) = v[ (translC c) , const "true" ]
  -- translS-Condition c false = v[ (translC c) , const "false" ]
  -- translS-Condition c true = v[ (translC c) , const "true" ]

  {- State Translation -}
  -- Given a state 𝕊 and a list of conditions ℙ, map each condition in ℙ
  -- to a PropAtom where the truth value reflects whether the condition is in
  -- the state.
  -- translS : ∀ (S : State) (P : List (Condition 0)) → Vec (Prop × Mode) (length P)
  -- translS S [] = []
  -- translS S (x ∷ P) = ⟨ ` translS-helper x (x ∈ᶜᵇ S) , Linear ⟩ ∷ translS S P
  translS-Conditions : ∀ { n } → List GroundCondition → ( cs : Vec GroundCondition n) → Vec (Prop × Mode) n
  translS-Conditions S [] = []
  translS-Conditions S (c ∷ cs) = ⟨ ` translS-Condition c (c ∈? S) , Linear ⟩ ∷ (translS-Conditions S cs)

  translS : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 → Vec (Prop × Mode) (length ℂ)
  translS (wf/prob _ ℂ 𝕀 _ _ _ _) = translS-Conditions 𝕀 ℂ
 