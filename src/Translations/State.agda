open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Plans.Domain

module Translations.State (domain : Domain) where
  open Domain domain

  infixl 30 var
  data Term : Set where
    true : Term
    false : Term
    var : ℕ → Term

  infix 10 v[_,_]
  data Proposition : Set where
    v[_,_] : Predicate → Term → Proposition


  translS : PredMap → Proposition
  translS ⟨ polarity , pred ⟩ with polarity
  ... | + = v[ pred , true ]
  ... | - = v[ pred , false ]