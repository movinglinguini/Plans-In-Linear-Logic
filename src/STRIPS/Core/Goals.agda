open import Data.Product
open import Data.Nat
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.Any
open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Bool
open import Data.Maybe
open import Relation.Nullary.Decidable

open import STRIPS.Core.Common

module STRIPS.Core.Goals where
  open import STRIPS.Core.States

  -- A goal is just state. We will make an alias for state
  -- for readability.
  Goal = State