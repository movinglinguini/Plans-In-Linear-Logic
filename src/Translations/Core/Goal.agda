open import Data.List hiding (_++_)
open import Data.Nat using (_+_)
open import Data.Vec hiding (length)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module Translations.Core.Goal where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props Proposition
  open import Logic.Core.Terms TermAtom

  private     
    -- Some helper functions for goal translation
    translhalf : (C : List (Condition 0)) → Bool → Vec Prop (length C)
    translhalf [] b = []
    translhalf (x ∷ C) false = ` v[ translC x , const "false" ] ∷ translhalf C false
    translhalf (x ∷ C) true = ` v[ translC x , const "true" ] ∷ translhalf C true 

  translG : (G : Goal) → Vec Prop (length (Goal.pos G) + length (Goal.neg G))
  translG G = (translhalf (Goal.pos G) true) ++ (translhalf (Goal.neg G) false)
  