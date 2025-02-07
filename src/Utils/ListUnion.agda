open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List
open import Relation.Nullary using (does)
open import Data.Bool using (true; false)

module Utils.ListUnion { A : Set } (_≟_ : DecidableEquality A) where
  open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

  infix 50 _∪_

  _∪_ : List A → List A → List A
  [] ∪ L = L
  L ∪ [] = L
  (x ∷ xs) ∪ ys with does (x ∈? ys)
  ... | false = x ∷ (xs ∪ ys)
  ... | true = xs ∪ ys