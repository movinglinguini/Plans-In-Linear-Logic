open import Data.Nat
open import Plans.Domain

module Syntax.Core (domain : Domain) where
  open Domain domain

  infixl 30 var
  data Term : Set where
    true : Term
    false : Term
    var : ℕ → Term

  infix 10 v[_,_]
  data Proposition : Set where
    v[_,_] : Predicate → Term → Proposition