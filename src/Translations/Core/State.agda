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
  
  -- We are ultimately translating Conditions into Propositions,
  -- which contain translated conditions (TCondition) + a truth value term.
  infix 10 v[_,_]
  data Proposition : Set where
    v[_,_] : TCondition → Term → Proposition

  open import Logic.Core.Props Proposition
  open import Logic.Core.Modes
  open import Logic.Utils.ModeOf Proposition

  private
    variable
      s : ℕ
      𝕊 ℙ : List (Condition s)

    -- Helper function for translS
    -- Bool is supposed to represent whether or not the condition c was in the state we
    -- are translating over. If it is, then the proposition we translate to gets a truth
    -- value of "true". Otherwise, it gets "false".
    translS-helper : ∀ { s } → Condition s → Bool → Prop
    translS-helper c false = ` v[ (translC c) , const "false" ]
    translS-helper c true = ` v[ (translC c) , const "true" ]

  {- State Translation -}
  -- Given a state 𝕊 and a list of conditions ℙ, map each condition in ℙ
  -- to a proposition where the truth value reflects whether the condition is in
  -- the state.
  translS : ∀ { s } (𝕊 ℙ : List (Condition s)) → Vec (Prop × Mode) (length ℙ)
  translS 𝕊 [] = []
  translS 𝕊 (x ∷ ℙ) = ⟨ translS-helper x (x ∈ᶜᵇ 𝕊) , Linear ⟩ ∷ translS 𝕊 ℙ


