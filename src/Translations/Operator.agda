-- Translation of action descriptions from Actions You Can Handle into open 
-- lolli propositions in Adjoint Logic

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
  open import Data.List using (_++_; filterᵇ; unzip; map)

  open Domain domain
  
  open import Translations.State domain
  open import ADJ.Core Proposition public
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
  
    u≥l : Unrestricted ≥ Linear
    u≥l = StructRule.W ∷ʳ (StructRule.C ∷ʳ ∅)
  
  open import Utils.ListIntersection _≟_ public
  open import Utils.ListUnion _≟ₚ_ public

  private
    cond : List PredMap → List Predicate
    cond ∅ = ∅
    cond (⟨ pol , pred ⟩ , ps) = pred , cond ps

    buildProp : ∀ { m : Mode } → Prop m → ℕ → Prop m
    buildProp imp zero = imp
    buildProp imp (suc c) = all buildProp imp c

    translOhelper : ActionDescription       -- Original Action Description
                → List Predicate            -- Conditions of action description
                → Prop Linear               -- Left side of lolli, Initialized to 𝟙
                → Prop Linear               -- Right side of lolli, Initialized to 𝟙
                → ℕ                         -- Variable counter, initialized to 0
                → Prop Unrestricted
    translOhelper AD ∅ L R c = Up[ u≥l ] (buildProp (L ⊸ R) c)
    translOhelper AD (p , conds) L R c with does (⟨ + , p ⟩ ∈? ((AD ⁺) ∩ (AD ₊)))
    ... | true = translOhelper AD conds (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R) c
    ... | false with does (⟨ - , p ⟩ ∈? ((AD ⁻) ∩ (AD ₋)))
    ... | true = translOhelper AD conds (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R) c
    ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺)) ∧ does (⟨ - , p ⟩ ∈? (AD ₋))
    ... | true = translOhelper AD conds (` v[ p , true ] ⊗ L) (` v[ p , false ] ⊗ R) c
    ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻)) ∧ does (⟨ + , p ⟩ ∈? (AD ₊))
    ... | true = translOhelper AD conds (` v[ p , false ] ⊗ L) (` v[ p , true ] ⊗ R) c
    ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺))
    ... | true = translOhelper AD conds (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R) c
    ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻))
    ... | true = translOhelper AD conds (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R) c
    ... | false with does (⟨ + , p ⟩ ∈? (AD ₊))
    ... | true = translOhelper AD conds (` v[ p , var c ] ⊗ L) (` v[ p , true ] ⊗ R) (suc c)
    ... | false = translOhelper AD conds (` v[ p , var c ] ⊗ L) (` v[ p , false ] ⊗ R) (suc c)

  translO : ActionDescription → Prop Unrestricted
  translO AD = translOhelper AD (cond (ActionDescription.preconditions AD) ∪ cond (ActionDescription.effects AD)) 𝟙 𝟙 zero
