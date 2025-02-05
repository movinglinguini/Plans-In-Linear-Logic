open import Data.List
open import Plans.Domain

module Utils.ListToContext (domain : Domain) where
  open import ADJ.Core domain

  listToContext : ∀ { m } → List (Prop m) → Context
  listToContext [] = ∅ 
  listToContext (x ∷ Xs) = listToContext Xs , x