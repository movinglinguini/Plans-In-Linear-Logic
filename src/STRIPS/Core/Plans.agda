open import Data.List

module STRIPS.Core.Plans (TermAtom : Set) where
  open import STRIPS.Core.Operators TermAtom
  
  Plan = List Operator