open import Plans.Domain
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
      𝔾 : Goal
      𝔾ᵗ : Prop × Mode
    
    translatePos : Goal → List Prop
    translatePos g = Data.List.map (λ p → ` v[ (translC p) , (term "true") ]) (Goal.pos g) 

    translateNeg : Goal → List Prop
    translateNeg g = Data.List.map (λ p → ` v[ (translC p) , (term "false") ]) (Goal.pos g) 

    translg : Goal → List Prop
    translg G = (translatePos G) ++ (translateNeg G) 

  translG : Goal → Prop × Mode
  translG G = ⟨  (⨂ translg G) ⊗ ⊤ , Linear ⟩ 

  data TranslG : Goal → Prop × Mode → Set where
    translG/z : TranslG record { pos = [] ; neg = [] } ⟨ 𝟙 ⊗ ⊤ , Linear ⟩
    translG/s : TranslG 𝔾 (translG 𝔾)

  {- Properties of translation -}
  -- private
  --   isLinear : TranslG 𝔾 𝔾ᵗ → modeOf 𝔾ᵗ ≡ Linear
  --   isLinear transl/goal = refl
