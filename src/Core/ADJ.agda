{-
  Instantiates ADJ Logic with modes, a preorder on modes, a decidable preorder on modes, and a base type
  to construct propositions from.
-}

open import Mode using (Mode; StructRule; _,_; ∅)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊇_)
open import Relation.Binary.Definitions using (DecidableEquality)

module Core.ADJ (Predicate : Set) where
  -- Linear mode
  L : Mode
  L = record { structRules = ∅ }

  -- Unrestricted mode
  U : Mode
  U = record { structRules = StructRule.W , StructRule.C , ∅ }

  _≟_ : DecidableEquality StructRule
  StructRule.W ≟ StructRule.W = yes refl
  StructRule.W ≟ StructRule.C = no λ()
  StructRule.C ≟ StructRule.W = no λ()
  StructRule.C ≟ StructRule.C = yes refl

  open import Data.List.Relation.Binary.Sublist.DecPropositional _≟_ using (_⊆?_)

  _≥_ : Mode → Mode → Set
  m ≥ k = Mode.structRules m ⊇ Mode.structRules k

  _≥?_ : ∀ (m k : Mode)  → Dec (m ≥ k)
  m ≥? k with Mode.structRules k ⊆? Mode.structRules m
  ... | yes k⊆m = yes k⊆m
  ... | no ¬k⊆m = no  ¬k⊆m


  -- Make this instance of ADJ available
  open import ExplicitADJ Predicate L _≥_ _≥?_ public
  
