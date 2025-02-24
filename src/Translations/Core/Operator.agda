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
open import Data.Vec hiding (length; here; there)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any

module Translations.Core.Operator where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props Proposition
  open import Logic.Core.Terms TermAtom
  open import Logic.Core.Modes
  open import Logic.Utils.ModeOf Proposition

  private
    variable
      n : ℕ
      oᵗ : Prop × Mode
      Oᵗ : Vec (Prop × Mode) n

  private
    prependForAll : ℕ → Prop → Prop
    prependForAll zero P = P
    prependForAll (suc c) P = ∀[ prependForAll c P ]

    translPs : ℕ → List Condition → Operator → Prop → Prop → Prop
    translPs varCount [] o P₁ P₂ = prependForAll varCount (P₁ ⊸ P₂)
    translPs varCount (p ∷ Ps) o P₁ P₂ with (p ∈ᶜᵇ (o ⁺ ∩ᶜ o ₊))
    ... | true = translPs (varCount + (countVars p)) Ps o (` v[ translC p , term "true" ] ⊗ P₁) (` v[ translC p , term "true" ] ⊗ P₂)
    ... | false with (p ∈ᶜᵇ (o ⁻ ∩ᶜ o ₊))
    ... | true = translPs (varCount + (countVars p)) Ps o (` v[ translC p , term "false" ] ⊗ P₁) (` v[ translC p , term "true" ] ⊗ P₂)
    ... | false with (p ∈ᶜᵇ (o ⁺ ∩ᶜ o ₋))
    ... | true = translPs (varCount + (countVars p)) Ps o (` v[ translC p , term "true" ] ⊗ P₁) (` v[ translC p , term "false" ] ⊗ P₂)
    ... | false with (p ∈ᶜᵇ (o ⁻ ∩ᶜ o ₋))
    ... | true = translPs (varCount + (countVars p)) Ps o (` v[ translC p , term "false" ] ⊗ P₁) (` v[ translC p , term "false" ] ⊗ P₂)
    ... | false with ((p ∈ᶜᵇ o ⁺)) ∧ (not ((p ∈ᶜᵇ posts o)))
    ... | true = translPs (varCount + (countVars p)) Ps o (` v[ translC p , term "true" ] ⊗ P₁) (` v[ translC p , term "true" ] ⊗ P₂)
    ... | false with ((p ∈ᶜᵇ o ⁻)) ∧ (not ((p ∈ᶜᵇ posts o)))
    ... | true = translPs (varCount + (countVars p)) Ps o (` v[ translC p , term "false" ] ⊗ P₁) (` v[ translC p , term "true" ] ⊗ P₂)
    ... | false with ((p ∈ᶜᵇ o ₊)) ∧ (not ((p ∈ᶜᵇ pres o)))
    ... | true = translPs (suc (varCount + (countVars p))) Ps o (` v[ translC p , var (varCount + (countVars p)) ] ⊗ P₁) (` v[ translC p , term "true" ] ⊗ P₂)
    ... | false = translPs (suc (varCount + (countVars p))) Ps o (` v[ translC p , var (varCount + (countVars p)) ] ⊗ P₁) (` v[ translC p , term "false" ] ⊗ P₂)
  
  translO : Operator → Prop × Mode
  translO o = ⟨ translPs zero ((o ⁺ ∪ᶜ o ⁻) ∪ᶜ (o ₊ ∪ᶜ o ₋)) o 𝟙 𝟙 , Unrestricted ⟩

  translOs : (O : List Operator) → Vec (Prop × Mode) (Data.List.length O)
  translOs [] = []
  translOs (x ∷ O) = translO x ∷ translOs O 

  {- Properties of the translation -}
  data TranslO : Operator → Prop × Mode → Set where
    transl/op : TranslO o (translO o)

  data TranslOs : ∀ ( O : List Operator ) → Vec (Prop × Mode) (Data.List.length O) → Set where
    transl/ops/z : TranslOs [] []
    transl/ops/s : TranslOs O Oᵗ → TranslO o oᵗ
      ----------------------
      → TranslOs (o ∷ O) (oᵗ ∷ Oᵗ)
