open import Plans.Domain
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)

import ADJ.Core
import Utils.BigTensor

module Translations.Goal (domain : Domain) where

  open Domain domain

  open import Syntax.Core domain
  open ADJ.Core Proposition Term
  open Utils.BigTensor Proposition Term using (⨂_)

  private
    translPredmap : PredMap → Proposition
    translPredmap ⟨ polarity , pred ⟩ with polarity
    ... | + = v[ pred , true ]
    ... | - = v[ pred , false ]

  translG : GoalState → Prop Linear
  translG G = ⨂ Data.List.map `_ (Data.List.map translPredmap G)
