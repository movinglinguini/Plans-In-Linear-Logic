open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List
open import Relation.Nullary using (does)
open import Data.Bool using (true; false)

module Utils.ListIntersection { A : Set } (_≟_ : DecidableEquality A) where

  open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

  _∩_ : List A → List A → List A
  [] ∩ L = []
  L ∩ [] = []
  (x ∷ xs) ∩ ys with does (x ∈? ys)
  ... | true = x ∷ (xs ∩ ys)
  ... | false = xs ∩ ys