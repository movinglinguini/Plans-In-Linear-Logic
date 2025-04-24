open import Data.List
open import Data.Vec hiding (length)
open import Data.Product
open import Data.Bool


open import STRIPS.Problem

open import Translations.Core.PropAtom
open import Translations.Core.Condition

module Translations.Core.ConditionConfiguration where
  open import Logic.Core.Props PropAtom
  open import Logic.Core.Terms TermAtom renaming (Term to AdjointTerm)

  {-
    Translation of a condition configuration into a vector of prop atoms.
  -}
  translConfig-Condition : GroundCondition × Bool → Prop
  translConfig-Condition (c , false) = ` v[ translC c , const "false" ]
  translConfig-Condition (c , true) = ` v[ translC c , const "true" ]

  translConfig : (gs : List (GroundCondition × Bool)) → Vec Prop (length gs)
  translConfig [] = []
  translConfig ((c , false) ∷ gs) = (translConfig-Condition (c , false)) ∷ (translConfig gs)
  translConfig ((c , true) ∷ gs) = (translConfig-Condition (c , true)) ∷ (translConfig gs)