open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Vec hiding (length)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Data.Vec.Membership.Propositional

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
  translS 𝕊 (x ∷ ℙ) = ⟨ translS-helper x (does (x ∈ᶜ? 𝕊)) , Linear ⟩ ∷ translS 𝕊 ℙ

  {- Relation between state and its translation -}
  data TranslS : ∀ (𝕊 ℙ : List Condition) → Vec (Prop × Mode) (length ℙ) → Set where
    translS/z : ∀ { 𝕊 : List Condition } → TranslS 𝕊 [] []

    translS/s/true : ∀ { 𝕡 : Condition } { 𝕊 ℙ : List Condition } { 𝕊ᵗ : Vec (Prop × Mode) (length ℙ) } 
      → TranslS 𝕊 ℙ 𝕊ᵗ → 𝕡 ∈ᶜ 𝕊
      --------------------
      → TranslS 𝕊 (𝕡 ∷ ℙ) (⟨ ` v[ translC 𝕡 , term "true" ] , Linear ⟩ ∷ 𝕊ᵗ)

    translS/s/false : ∀ { 𝕡 : Condition } { 𝕊 ℙ : List Condition } { 𝕊ᵗ : Vec (Prop × Mode) (length ℙ) } 
      → TranslS 𝕊 ℙ 𝕊ᵗ → ¬ (𝕡 ∈ᶜ 𝕊)
      --------------------
      → TranslS 𝕊 (𝕡 ∷ ℙ) (⟨ ` v[ translC 𝕡 , term "false" ] , Linear ⟩ ∷ 𝕊ᵗ)

  {- Unary relation on state translations -}
  data AllLinear : ∀ { n } → Vec (Prop × Mode) n → Set where
    allLinear/z : AllLinear []

    allLinear/s : ∀ { n } { 𝕤ᵗ : Prop × Mode } { 𝕊ᵗ : Vec (Prop × Mode) n }
      → AllLinear 𝕊ᵗ → modeOf 𝕤ᵗ ≡ Linear
      -------------------------------------
      → AllLinear (𝕤ᵗ ∷ 𝕊ᵗ)

  {- Properties of the translation -}
  translS-all-linear : ∀ { 𝕊ᵗ : Vec (Prop × Mode) (length ℙ) } → TranslS 𝕊 ℙ 𝕊ᵗ → AllLinear 𝕊ᵗ
  translS-all-linear {ℙ = []} {𝕊ᵗ = []} trans = allLinear/z
  translS-all-linear {ℙ = 𝕡 ∷ ℙ} {𝕊ᵗ = ⟨ fst , snd ⟩ ∷ 𝕊ᵗ} (translS/s/true trans₁ x) = allLinear/s (translS-all-linear trans₁) refl
  translS-all-linear {ℙ = 𝕡 ∷ ℙ} {𝕊ᵗ = ⟨ fst , snd ⟩ ∷ 𝕊ᵗ} (translS/s/false trans₁ x) = allLinear/s (translS-all-linear trans₁) refl 

