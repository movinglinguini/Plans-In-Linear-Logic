-- Translation of action descriptions from Actions You Can Handle into open 
-- lolli propositions in Adjoint Logic
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool hiding (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no; does; contradiction; contraposition)
open import Relation.Nullary.Negation
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Core using (_∷ʳ_) renaming ([] to ∅)
open import Data.String hiding (_++_; length) renaming (_≟_ to _≟ₛ_)
open import Data.Nat using (ℕ; suc; zero; _+_) renaming (_≟_ to _≟ₙ_)
open import Data.Fin hiding (_+_)
open import Data.Vec

module Translations.Core.Operator where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props Proposition
  open import Logic.Core.Terms TermAtom
  open import Logic.Core.Modes
  open import Logic.Utils.ModeOf Proposition

  private
    -- Prepends n ∀'s before the given Prop
    prependForAlls : ∀ ( n : ℕ ) → Prop → Prop
    prependForAlls zero P = P
    prependForAlls (suc c) P = ∀[ prependForAlls c P ]

    -- Constructs an implication with universally quantified variables out of an operator o.
    translPs : ∀ ( o : Operator ) 
                → ℕ -- The count of truth value variables generated by the translation, to be initialized with zero
                → List (Condition (Operator.arity o)) -- To be initialized with all conditions of o
                → Prop -- To be initialized with 𝟙, and meant to be ⊗′d with translations of preconditions of o
                → Prop -- To be initialized with 𝟙, and meant to be ⊗'d with translations of postconditions of o
                → Prop

    translPs o tvc [] PL PR = prependForAlls ((Operator.arity o) + tvc) (PL ⊸ PR)
    translPs o tvc (p ∷ Ps) PL PR with (p ∈ᶜᵇ (o ⁺ ∩ᶜ o ₊))
    ... | true = translPs o tvc Ps (` v[ translC p , const "true" ] ⊗ PL) (` v[ translC p , const "true" ] ⊗ PR)
    ... | false with (p ∈ᶜᵇ (o ⁻ ∩ᶜ o ₊))
    ... | true = translPs o tvc Ps (` v[ translC p , const "false" ] ⊗ PL) (` v[ translC p , const "true" ] ⊗ PR)
    ... | false with (p ∈ᶜᵇ (o ⁺ ∩ᶜ o ₋))
    ... | true = translPs o tvc Ps (` v[ translC p , const "true" ] ⊗ PL) (` v[ translC p , const "false" ] ⊗ PR)
    ... | false with (p ∈ᶜᵇ (o ⁻ ∩ᶜ o ₋))
    ... | true = translPs o tvc Ps (` v[ translC p , const "false" ] ⊗ PL) (` v[ translC p , const "false" ] ⊗ PR)
    ... | false with ((p ∈ᶜᵇ o ⁺)) ∧ (not ((p ∈ᶜᵇ posts o)))
    ... | true = translPs o tvc Ps (` v[ translC p , const "true" ] ⊗ PL) (` v[ translC p , const "true" ] ⊗ PR)
    ... | false with ((p ∈ᶜᵇ o ⁻)) ∧ (not ((p ∈ᶜᵇ posts o)))
    ... | true = translPs o tvc Ps (` v[ translC p , const "false" ] ⊗ PL) (` v[ translC p , const "true" ] ⊗ PR)
    ... | false with ((p ∈ᶜᵇ o ₊)) ∧ (not ((p ∈ᶜᵇ pres o)))
    ... | true = translPs o (suc tvc) Ps (` v[ translC p , var ((Operator.arity o) + tvc) ] ⊗ PL) (` v[ translC p , const "true" ] ⊗ PR)
    ... | false = translPs o (suc tvc) Ps (` v[ translC p , var ((Operator.arity o) + tvc) ] ⊗ PL) (` v[ translC p , const "false" ] ⊗ PR)
  
  {- 
    Given an operator, translates into a universally quantified unrestricted implication. 
    See the pretty-printed translation example below for what this is supposed to look like.
  -}
  translO : Operator → Prop × Mode
  translO o = ⟨ (translPs o zero ((o ⁺ ∪ᶜ o ⁻) ∪ᶜ (o ₊ ∪ᶜ o ₋)) 𝟙 𝟙) , Unrestricted ⟩

  translOs : (O : List Operator) → Vec (Prop × Mode) (Data.List.length O)
  translOs [] = []
  translOs (x ∷ O) = translO x ∷ translOs O 

  -- Let's test translO
  private
    o : Operator
    o = record
      { label = "stack"
      ; arity = 2
      ; posPre = (record { name = "holding" 
                        ; terms = var zero ∷ [] }) ∷ 
                  record { name = "clear" 
                        ; terms = var (suc zero) ∷ [] } 
                  ∷ []
      ; negPre = []
      ; posPost = (record { name = "clear" 
                        ; terms = var zero ∷ [] }) ∷ 
                  record { name = "handempty" 
                        ; terms = [] } ∷ 
                  record { name = "on"
                        ; terms = var zero ∷ var (suc zero) ∷ [] } ∷ []
      ; negPost = (record { name = "holding" 
                        ; terms = var zero ∷ [] }) ∷ 
                  record { name = "clear" 
                        ; terms = var (suc zero) ∷ [] } 
                  ∷ []
      }

  o-trans : Prop × Mode
  o-trans = translO o
  
  open import PrettyPrinter.PrettyPrinter 3000

  -- Pretty printing the result instead of using an equality test because
  -- writing the result out by hand is very tedious.
  o-trans-str = render (prettyProp (proj₁ o-trans)) 
