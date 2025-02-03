-- Translation of action descriptions from Actions You Can Handle into open 
-- lolli propositions in Adjoint Logic
open import Data.List using (List; _++_; filterᵇ; unzip; map; []; _∷_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool hiding (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no; does; contradiction; contraposition)
open import Relation.Nullary.Negation
open import Plans.Domain
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Core using (_∷ʳ_) renaming ([] to ∅)
open import Data.String hiding (_++_) renaming (_≟_ to _≟ₛ_)
open import Data.Nat using (ℕ; suc; zero) renaming (_≟_ to _≟ₙ_)

module Translations.Operator (domain : Domain) where
  open Domain domain
  
  open import Syntax.Core domain
  
  open import ADJ.Core domain
  open import Utils.BigTensor Proposition using (⨂_)
  open import Utils.PredMap.DecEquality domain

  private 
    isPos : PredMap → Bool
    isPos ⟨ + , p ⟩ = true
    isPos ⟨ - , p ⟩ = false

    isNeg : PredMap → Bool
    isNeg p with isPos p
    ... | true = false
    ... | false = true

    filterPositive : List PredMap → List PredMap
    filterPositive L = filterᵇ isPos L
        
    filterNegative : List PredMap → List PredMap
    filterNegative L = filterᵇ isNeg L

    _⁺ : ActionDescription → List PredMap
    o ⁺ = filterPositive (ActionDescription.preconditions o)

    _⁻ : ActionDescription → List PredMap
    o ⁻ = filterNegative (ActionDescription.preconditions o)

    _₊ : ActionDescription → List PredMap
    o ₊ = filterPositive (ActionDescription.effects o)

    _₋ : ActionDescription → List PredMap
    o ₋ = filterNegative (ActionDescription.effects o)
  
  open import Utils.ListIntersection _≟_
  open import Utils.ListUnion _≟ₚ_

  private
    cond : List PredMap → List Predicate
    cond [] = []
    cond (⟨ fst , snd ⟩ ∷ ps) = snd ∷ cond ps

    prependForAll : ℕ → Prop → Prop
    prependForAll zero P = P
    prependForAll (suc c) P = ∀[ prependForAll c P ]

    translPs : ℕ → List Predicate → ActionDescription → Prop → Prop → Prop × Mode
    translPs c [] AD L R = ⟨ prependForAll c (L ⊸ R) , Unrestricted ⟩
    translPs c (p ∷ Ps) AD L R with does (⟨ + , p ⟩ ∈? ((AD ⁺) ∩ (AD ₊)))
    ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R)
    ... | false with does (⟨ - , p ⟩ ∈? ((AD ⁻) ∩ (AD ₋)))
    ... | true = translPs c Ps AD (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R)
    ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺)) ∧ does (⟨ - , p ⟩ ∈? (AD ₋))
    ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , false ] ⊗ R)
    ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻)) ∧ does (⟨ + , p ⟩ ∈? (AD ₊))
    ... | true = translPs c Ps AD (` v[ p , false ] ⊗ L) (` v[ p , true ] ⊗ R)
    ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺))
    ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R)
    ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻))
    ... | true = translPs c Ps AD  (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R)
    ... | false with does (⟨ + , p ⟩ ∈? (AD ₊))
    ... | true = translPs (suc c) Ps AD (` v[ p , var c ] ⊗ L) (` v[ p , true ] ⊗ R)
    ... | false = translPs (suc c) Ps AD (` v[ p , var c ] ⊗ L) (` v[ p , false ] ⊗ R)

  translO : ActionDescription → Prop × Mode
  translO AD = translPs zero ((cond (ActionDescription.preconditions AD)) ∪ cond (ActionDescription.effects AD)) AD 𝟙 𝟙

  