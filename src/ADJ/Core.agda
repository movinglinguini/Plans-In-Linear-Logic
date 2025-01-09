{-
  Instantiates ADJ Logic with modes, a preorder on modes, a decidable preorder on modes, and a base type
  to construct propositions from.
-}
open import Data.List using (List) renaming(_∷_ to _,_; [] to ∅)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊇_)
open import Relation.Binary.Definitions using (DecidableEquality)

-- TODO: Decide if T needs to stay
module ADJ.Core (U : Set) (T : Set) where
  -- Bundle up and export pieces of ADJ
  open import ADJ.Mode using (Mode; StructRule) public
  
  -- Linear mode
  Linear : Mode
  Linear = record { structRules = ∅ }

  -- Unrestricted mode
  Unrestricted : Mode
  Unrestricted = record { structRules = StructRule.W , StructRule.C , ∅ }
  
  private
    _≟_ : DecidableEquality StructRule
    StructRule.W ≟ StructRule.W = yes refl
    StructRule.W ≟ StructRule.C = no λ()
    StructRule.C ≟ StructRule.W = no λ()
    StructRule.C ≟ StructRule.C = yes refl

  open import Data.List.Relation.Binary.Sublist.DecPropositional _≟_ using (_⊆?_)

  -- Our preorder on modes
  _≥_ : Mode → Mode → Set
  m ≥ k = Mode.structRules m ⊇ Mode.structRules k

  -- Decidable preorder on modes
  _≥?_ : ∀ (m k : Mode)  → Dec (m ≥ k)
  m ≥? k with Mode.structRules k ⊆? Mode.structRules m
  ... | yes k⊆m = yes k⊆m
  ... | no ¬k⊆m = no  ¬k⊆m

  -- Make this instance of ADJ available
  open import ADJ.ADJE U T Linear _≥_ _≥?_ as ADJ-UL public
  
