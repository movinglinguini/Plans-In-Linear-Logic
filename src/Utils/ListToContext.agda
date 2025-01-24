open import Data.List

module Utils.ListToContext (U : Set) (T : Set) where
  open import ADJ.Core U T

  listToContext : ∀ { m } → List (Prop m) → Context
  listToContext [] = ∅ 
  listToContext (x ∷ Xs) = listToContext Xs , x