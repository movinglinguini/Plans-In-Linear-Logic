-- Translation of action descriptions from Actions You Can Handle into open 
-- lolli propositions in Adjoint Logic
open import Data.List using (List; _++_; filterᵇ; unzip; map; []; _∷_; length)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool hiding (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no; does; contradiction; contraposition)
open import Relation.Nullary.Negation
open import Plans.Domain
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Core using (_∷ʳ_) renaming ([] to ∅)
open import Data.String hiding (_++_; length) renaming (_≟_ to _≟ₛ_)
open import Data.Nat using (ℕ; suc; zero) renaming (_≟_ to _≟ₙ_)
open import Data.Vec hiding (length)

module Translations.Operator where
  open import Syntax.Core
  open import STRIPS.Problem
  open import Logic.Core.Props Proposition
  open import Logic.Core.Modes
  open import Translations.Condition

  private
    prependForAll : ℕ → Prop → Prop
    prependForAll zero P = P
    prependForAll (suc c) P = ∀[ prependForAll c P ]

    translPs : ℕ → List Condition → Operator → Prop → Prop → Prop × Mode
    translPs varCount [] o P₁ P₂ = ⟨ prependForAll varCount (P₁ ⊸ P₂) , Unrestricted ⟩
    translPs varCount (p ∷ Ps) o P₁ P₂ with does (p ∈ᶜ? (o ⁺ ∩ᶜ o ₊))
    ... | false = translPs varCount Ps o (` v[ translC p , term "true" ] ⊗ P₁) (` v[ translC p , term "true" ] ⊗ P₂)
    ... | true = {!   !}
    -- translPs c [] AD L R = ⟨ prependForAll c (L ⊸ R) , Unrestricted ⟩
    -- translPs c (p ∷ Ps) AD L R with does (⟨ + , p ⟩ ∈? ((AD ⁺) ∩ (AD ₊)))
    -- ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R)
    -- ... | false with does (⟨ - , p ⟩ ∈? ((AD ⁻) ∩ (AD ₋)))
    -- ... | true = translPs c Ps AD (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R)
    -- ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺)) ∧ does (⟨ - , p ⟩ ∈? (AD ₋))
    -- ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , false ] ⊗ R)
    -- ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻)) ∧ does (⟨ + , p ⟩ ∈? (AD ₊))
    -- ... | true = translPs c Ps AD (` v[ p , false ] ⊗ L) (` v[ p , true ] ⊗ R)
    -- ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺))
    -- ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R)
    -- ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻))
    -- ... | true = translPs c Ps AD  (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R)
    -- ... | false with does (⟨ + , p ⟩ ∈? (AD ₊))
    -- ... | true = translPs (suc c) Ps AD (` v[ p , var c ] ⊗ L) (` v[ p , true ] ⊗ R)
    -- ... | false = translPs (suc c) Ps AD (` v[ p , var c ] ⊗ L) (` v[ p , false ] ⊗ R)
  
  translO : Operator → Prop × Mode
  translO o = translPs zero ((o ⁺ ∪ᶜ o ⁻) ∪ᶜ (o ₊ ∪ᶜ o ₋)) o 𝟙 𝟙

-- module Translations.Operator (domain : Domain) where
--   open Domain domain
  
--   open import Syntax.Core domain
  
--   open import ADJ.Core domain renaming (Context to AdjContext)
--   open import Utils.BigTensor domain using (⨂_)
--   open import Utils.PredMap.DecEquality domain

--   variable
--     𝕠 : ActionDescription
--     𝕆 : List ActionDescription
--     𝕆ᵗ : Vec (Prop × Mode) n
--     𝕠ᵗ : Prop × Mode

--   private 
--     isPos : PredMap → Bool
--     isPos ⟨ + , p ⟩ = true
--     isPos ⟨ - , p ⟩ = false

--     isNeg : PredMap → Bool
--     isNeg p with isPos p
--     ... | true = false
--     ... | false = true

--     filterPositive : List PredMap → List PredMap
--     filterPositive L = filterᵇ isPos L
        
--     filterNegative : List PredMap → List PredMap
--     filterNegative L = filterᵇ isNeg L

--     _⁺ : ActionDescription → List PredMap
--     o ⁺ = filterPositive (ActionDescription.preconditions o)

--     _⁻ : ActionDescription → List PredMap
--     o ⁻ = filterNegative (ActionDescription.preconditions o)

--     _₊ : ActionDescription → List PredMap
--     o ₊ = filterPositive (ActionDescription.effects o)

--     _₋ : ActionDescription → List PredMap
--     o ₋ = filterNegative (ActionDescription.effects o)
  
--   open import Utils.ListIntersection _≟_
--   open import Utils.ListUnion _≟ₚ_

--   private
--     cond : List PredMap → List Predicate
--     cond [] = []
--     cond (⟨ fst , snd ⟩ ∷ ps) = snd ∷ cond ps

--     prependForAll : ℕ → Prop → Prop
--     prependForAll zero P = P
--     prependForAll (suc c) P = ∀[ prependForAll c P ]

--     translPs : ℕ → List Predicate → ActionDescription → Prop → Prop → Prop × Mode
--     translPs c [] AD L R = ⟨ prependForAll c (L ⊸ R) , Unrestricted ⟩
--     translPs c (p ∷ Ps) AD L R with does (⟨ + , p ⟩ ∈? ((AD ⁺) ∩ (AD ₊)))
--     ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R)
--     ... | false with does (⟨ - , p ⟩ ∈? ((AD ⁻) ∩ (AD ₋)))
--     ... | true = translPs c Ps AD (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R)
--     ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺)) ∧ does (⟨ - , p ⟩ ∈? (AD ₋))
--     ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , false ] ⊗ R)
--     ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻)) ∧ does (⟨ + , p ⟩ ∈? (AD ₊))
--     ... | true = translPs c Ps AD (` v[ p , false ] ⊗ L) (` v[ p , true ] ⊗ R)
--     ... | false with does (⟨ + , p ⟩ ∈? (AD ⁺))
--     ... | true = translPs c Ps AD (` v[ p , true ] ⊗ L) (` v[ p , true ] ⊗ R)
--     ... | false with does (⟨ - , p ⟩ ∈? (AD ⁻))
--     ... | true = translPs c Ps AD  (` v[ p , false ] ⊗ L) (` v[ p , false ] ⊗ R)
--     ... | false with does (⟨ + , p ⟩ ∈? (AD ₊))
--     ... | true = translPs (suc c) Ps AD (` v[ p , var c ] ⊗ L) (` v[ p , true ] ⊗ R)
--     ... | false = translPs (suc c) Ps AD (` v[ p , var c ] ⊗ L) (` v[ p , false ] ⊗ R)

--   translO : ActionDescription → Prop × Mode
--   translO AD = translPs zero ((cond (ActionDescription.preconditions AD)) ∪ cond (ActionDescription.effects AD)) AD 𝟙 𝟙

--   data TranslOs : ∀ ( 𝕆 : List ActionDescription ) → Vec (Prop × Mode) (length 𝕆) → Set where
--     Z : TranslOs [] []

--     S : TranslOs 𝕆 𝕆ᵗ
--       -----------------------
--       → TranslOs (𝕠 ∷ 𝕆) (translO 𝕠 ∷ 𝕆ᵗ)

--   data OContext : Vec (Prop × Mode) n → AdjContext 2 n → Set where
--     Z : OContext [] ⟨ term true ∷ term false ∷ [] , [] ⟩

--     S : OContext 𝕆ᵗ Δ
--       -----------------------
--       → OContext (𝕠ᵗ ∷ 𝕆ᵗ) (⟨ term true ∷ term false ∷ [] , 𝕠ᵗ ∷ proj₂ Δ ⟩)
    
 
   