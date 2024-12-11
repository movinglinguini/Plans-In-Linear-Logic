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

module Translations.Operator (domain : Domain) (Term : Set) where
  open import Data.List using (_++_; filterᵇ; unzip; map)

  open Domain domain
  open import Plans.PredMap.Properties domain
  
  open import ADJ.Core PredMap Term public
  open import Utils.BigTensor PredMap Term using (⨂_)

  private 
    isPos : PredMap → Bool
    isPos ⟨ + , p ⟩ = true
    isPos ⟨ - , p ⟩ = false
    isPos ⟨ polvar x , p ⟩ = false

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
    ... | true = translOhelper AD conds (` ⟨ + , p ⟩ ⊗ L) (` ⟨ + , p ⟩ ⊗ R) c
    ... | false with does (⟨ - , p ⟩ ∈? ((AD ⁻) ∩ (AD ₋)))
    ... | true = translOhelper AD conds (` ⟨ - , p ⟩ ⊗ L) (` ⟨ - , p ⟩ ⊗ R) c
    ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺)) ∧ does (⟨ - , p ⟩ ∈? (AD ₋))
    ... | true = translOhelper AD conds (` ⟨ + , p ⟩ ⊗ L) (` ⟨ - , p ⟩ ⊗ R) c
    ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻)) ∧ does (⟨ + , p ⟩ ∈? (AD ₊))
    ... | true = translOhelper AD conds (` ⟨ - , p ⟩ ⊗ L) (` ⟨ + , p ⟩ ⊗ R) c
    ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺))
    ... | true = translOhelper AD conds (` ⟨ + , p ⟩ ⊗ L) (` ⟨ + , p ⟩ ⊗ R) c
    ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻))
    ... | true = translOhelper AD conds (` ⟨ - , p ⟩ ⊗ L) (` ⟨ - , p ⟩ ⊗ R) c
    ... | false with does (⟨ + , p ⟩ ∈? (AD ₊))
    ... | true = translOhelper AD conds (` ⟨ polvar c , p ⟩ ⊗ L) (` ⟨ + , p ⟩ ⊗ R) (suc c)
    ... | false = translOhelper AD conds (` ⟨ polvar c , p ⟩ ⊗ L) (` ⟨ - , p ⟩ ⊗ R) (suc c)
    -- translOhelper AD (⟨ pol , p ⟩ Data.List.∷ conds) L R c with does (⟨ pol , p ⟩ ∈? ((AD ⁺) ∩ (AD ₊)))
    -- ... | true = translOhelper AD conds (` (⟨ pol , p ⟩) ⊗ L) (` (⟨ pol , p ⟩) ⊗ R) c
    -- ... | false with does (⟨ pol , p ⟩ ∈? ((AD ⁻) ∩ (AD ₋)))
    -- ... | true = translOhelper AD conds ((` (⟨ pol , p ⟩) ⊗ L)) ((` (⟨ pol , p ⟩) ⊗ R)) c
    -- ... | false with does (⟨ pol , p ⟩ ∈? (AD ⁺)) ∧ does (⟨ - , p ⟩ ∈? (AD ₋))
    -- ... | true = translOhelper AD conds ((` (⟨ pol , p ⟩) ⊗ L)) ((` (⟨ - , p ⟩) ⊗ R)) c
    -- ... | false with does (⟨ pol , p ⟩ ∈? (AD ⁻)) ∧ does (⟨ + , p ⟩ ∈? (AD ₊))
    -- ... | true = translOhelper AD conds ((` (⟨ pol , p ⟩) ⊗ L)) ((` (⟨ + , p ⟩) ⊗ R)) c
    -- ... | false with does (⟨ pol , p ⟩ ∈? (AD ⁺))
    -- ... | true = translOhelper AD conds (` (⟨ pol , p ⟩) ⊗ L) (` (⟨ pol , p ⟩) ⊗ R) c
    -- ... | false with does (⟨ pol , p ⟩ ∈? (AD ⁻))
    -- ... | true = translOhelper AD conds (` (⟨ pol , p ⟩) ⊗ L) (` (⟨ pol , p ⟩) ⊗ R) c
    -- ... | false with does (⟨ pol , p ⟩ ∈? (AD ₊))
    -- ... | true = translOhelper AD conds (` (⟨ polvar c , p ⟩) ⊗ L) (` (⟨ pol , p ⟩) ⊗ R) (suc c)
    -- ... | false with does (⟨ pol , p ⟩ ∈? (AD ₋))
    -- ... | true = translOhelper AD conds (` (⟨ polvar c , p ⟩) ⊗ L) (` (⟨ pol , p ⟩) ⊗ R) (suc c)
    -- ... | false = 𝟙 ⊸ 𝟙 -- An error must have occurred to get here

  translO : ActionDescription → Prop Unrestricted
  translO AD = translOhelper AD (cond (ActionDescription.preconditions AD) ∪ cond (ActionDescription.effects AD)) 𝟙 𝟙 zero
  -- translO AD = translOhelper AD (cond AD) 𝟙 𝟙 zero
  -- translO : ActionDescription → Prop Unrestricted
  -- translO o = Up[ u≥l ] (P₁ ⊸ P₂)
  --   where
  --     P₁ : Prop Linear
  --     P₂ : Prop Linear

  --     o⁺ = filterPositive (ActionDescription.preconditions o)
  --     o⁻ = filterNegative (ActionDescription.preconditions o)
  --     o₊ = filterPositive (ActionDescription.effects o)
  --     o₋ = filterNegative (ActionDescription.effects o)

  --     translP : PredMap → ActionDescription → (Prop Linear) × (Prop Linear)
  --     translP p o with does (p ∈? o⁺) | does (p ∈? o₊)
  --     ... | false | true = ⟨ ∀[ "x" ] (` ⟨ polvar "x" , proj₂ p ⟩) , ` p ⟩
  --     ... | true | false = ⟨ ` p , ` p ⟩
  --     ... | true | true =  ⟨ ` p , ` p ⟩
  --     ... | false | false with does (p ∈? o⁻) | does (p ∈? o₋)
  --     ... | false | false = ⟨ 𝟙 , 𝟙 ⟩
  --     ... | false | true = ⟨ ∀[ "x" ] (` ⟨ polvar "x" , proj₂ p ⟩) , ` p ⟩
  --     ... | true | false = ⟨ ` p , ` p ⟩
  --     ... | true | true = ⟨ ` p , ` p ⟩       
      
  --     Ps : (List (Prop Linear)) × (List (Prop Linear))
  --     Ps = unzip (Data.List.map (λ p → translP p o) (cond o))

  --     P₁ = ⨂ proj₁ Ps
  --     P₂ = ⨂ proj₂ Ps
   