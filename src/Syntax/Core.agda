open import Data.Nat
open import Plans.Domain

module Syntax.Core where
  open import STRIPS.Problem
  open import Translations.Condition

  infix 10 v[_,_]
  data Proposition : Set where
    v[_,_] : TCondition → Term → Proposition


