open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Plans.Domain

module Utils.PredMapToProposition (domain : Domain) where

  open Domain domain
  open import Syntax.Core domain

  translPredmap : PredMap → Proposition
  translPredmap ⟨ polarity , pred ⟩ with polarity
  ... | + = v[ pred , true ]
  ... | - = v[ pred , false ]