open import Plans.Domain
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Translations.Goal (domain : Domain) where

  open Domain domain

  open import Syntax.Core domain
  open import ADJ.Core domain
  open import Utils.BigTensor Proposition using (⨂_)
  open import Utils.PredMapToProposition domain


  translG : GoalState → Prop
  translG G = ⨂ Data.List.map `_ (Data.List.map translPredmap G) 
