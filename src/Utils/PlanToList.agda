open import Data.List
open import Plans.Domain

module Utils.PlanToList (domain : Domain) where
  open Domain domain

  open import Plans.Plan domain

  planToList : Plan → List Action
  planToList halt = []
  planToList (α ∷ P) = α ∷ planToList P
