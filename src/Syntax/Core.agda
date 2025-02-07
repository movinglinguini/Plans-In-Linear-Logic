open import Data.Nat
open import Plans.Domain

module Syntax.Core (TermAtom : Set) where
  open import STRIPS.Core.Conditions TermAtom
  open import STRIPS.Core.Terms TermAtom

  infix 10 v[_,_]
  data Proposition : Set where
    v[_,_] : Condition → Term → Proposition
