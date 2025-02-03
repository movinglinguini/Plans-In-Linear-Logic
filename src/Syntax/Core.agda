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

  substProposition : Proposition → Term → Proposition
  substProposition v[ x , true ] t = v[ x , true ] 
  substProposition v[ x , false ] t = v[ x , false ]
  substProposition v[ x , var x₁ ] t = v[ x , t ]
  