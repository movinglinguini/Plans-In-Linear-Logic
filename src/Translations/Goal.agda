open import Plans.Domain
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Translations.Goal (domain : Domain) where

  open Domain domain

  open import Syntax.Core domain
  open import ADJ.Core domain
  open import Utils.BigTensor domain using (⨂_)
  open import Utils.PredMapToProposition domain

  variable
    𝔾 : GoalState
    𝔾ᵗ : Prop
    g : PredMap

  translG : GoalState → Prop
  translG G = ⨂ Data.List.map `_ (Data.List.map translPredmap G) 

  data TranslG : GoalState → Prop → Set where
    Z : TranslG [] 𝟙
    
    S : 
      TranslG 𝔾 𝔾ᵗ
      ------------------------------------------
      → TranslG (g ∷ 𝔾) (` (translPredmap g) ⊗ 𝔾ᵗ)
