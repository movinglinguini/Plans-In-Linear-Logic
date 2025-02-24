open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module Translations.Core.Goal where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props Proposition
  open import Logic.Core.Terms TermAtom
  open import Logic.Core.Modes
  open import Logic.Utils.ModeOf Proposition
  open import Utils.BigTensor Proposition

  private 
    variable
      G-pos G-neg : List Condition
      𝔾 : Goal
      𝔾ᵗ : Prop × Mode
    
    translatePos : Goal → List Prop
    translatePos g = Data.List.map (λ p → ` v[ (translC p) , (term "true") ]) (Goal.pos g) 

    translateNeg : Goal → List Prop
    translateNeg g = Data.List.map (λ p → ` v[ (translC p) , (term "false") ]) (Goal.neg g) 

    translg : Goal → List Prop
    translg G = (translatePos G) ++ (translateNeg G) 

  translG : Goal → Prop × Mode
  translG G = ⟨  (⨂ translg G) ⊗ ⊤ , Linear ⟩ 

  {- Properties of the translation -}
  translG-linear : ∀ { 𝔾 𝔾ᵗ } → 𝔾ᵗ ≡ translG 𝔾 → modeOf 𝔾ᵗ ≡ Linear
  translG-linear refl = refl
