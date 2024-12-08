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

module Translations.Operator (domain : Domain) (Term : Set) where
  open import Data.List using (_++_; filterᵇ; unzip; map)

  open Domain domain
  
  open import ADJ.Core PredMap Term public
  open import Utils.BigTensor PredMap Term using (⨂_)

  private 
    cond : ActionDescription → List (Polarity × Predicate)
    cond record { preconditions = preconditions ; effects = effects } = preconditions ++ effects

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
  
    u≥l : Unrestricted ≥ Linear
    u≥l = StructRule.W ∷ʳ (StructRule.C ∷ʳ ∅)

    postulate
      pols=pols : ∀ { x y : String } → (polvar x) ≡ (polvar y) → x ≡ y

    _≡pol?_ : DecidableEquality Polarity
    pol₁ ≡pol? pol₂ with pol₁ | pol₂
    ... | + | + = yes refl
    ... | + | - = no (λ())
    ... | + | polvar x = no λ ()
    ... | - | + = no (λ ())
    ... | - | - = yes refl
    ... | - | polvar x = no λ ()
    ... | polvar x | + = no λ ()
    ... | polvar x | - = no λ ()
    ... | polvar x | polvar y with x ≟ₛ y
    ... | yes refl = yes refl
    ... | no x!=y = no λ x₁ → x!=y (pols=pols x₁)

    postulate
      -- If pred maps are equal, then their constituents must be equal.
      pp=pp-1 : ∀ { pol₁ pol₂ : Polarity } { p₁ p₂ : Predicate } → ⟨ pol₁ , p₁ ⟩ ≡ ⟨ pol₂ , p₂ ⟩ → pol₁ ≡ pol₂
      pp=pp-2 : ∀ { pol₁ pol₂ : Polarity } { p₁ p₂ : Predicate } → ⟨ pol₁ , p₁ ⟩ ≡ ⟨ pol₂ , p₂ ⟩ → p₁ ≡ p₂

    _≟_ : DecidableEquality PredMap
    ⟨ pol₁ , p₁ ⟩ ≟ ⟨ pol₂ , p₂ ⟩ with pol₁ ≡pol? pol₂ | p₁ ≟ₚ p₂
    ... | yes refl | yes refl = yes refl
    ... | yes refl | no p!=p = no λ x → contradiction (pp=pp-2 x) p!=p
    ... | no pol!=pol | yes refl = no λ x → contradiction (pp=pp-1 x) pol!=pol 
    ... | no pol!=pol | no p!=p = no λ x → contradiction (pp=pp-2 x) p!=p
        

    open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

  translO : ActionDescription → Prop Unrestricted
  translO o = Up[ u≥l ] (P₁ ⊸ P₂)
    where
      P₁ : Prop Linear
      P₂ : Prop Linear

      o⁺ = filterPositive (ActionDescription.preconditions o)
      o⁻ = filterNegative (ActionDescription.preconditions o)
      o₊ = filterPositive (ActionDescription.effects o)
      o₋ = filterNegative (ActionDescription.effects o)

      translP : PredMap → ActionDescription → (Prop Linear) × (Prop Linear)
      translP p o with does (p ∈? o⁺) | does (p ∈? o₊)
      ... | false | true = ⟨ ∀[ "x" ] (` ⟨ polvar "x" , proj₂ p ⟩) , ` p ⟩
      ... | true | false = ⟨ ` p , ` p ⟩
      ... | true | true =  ⟨ ` p , ` p ⟩
      ... | false | false with does (p ∈? o⁻) | does (p ∈? o₋)
      ... | false | false = ⟨ 𝟙 , 𝟙 ⟩
      ... | false | true = ⟨ ∀[ "x" ] (` ⟨ polvar "x" , proj₂ p ⟩) , ` p ⟩
      ... | true | false = ⟨ ` p , ` p ⟩
      ... | true | true = ⟨ ` p , ` p ⟩       
      
      Ps : (List (Prop Linear)) × (List (Prop Linear))
      Ps = unzip (Data.List.map (λ p → translP p o) (cond o))

      P₁ = ⨂ proj₁ Ps
      P₂ = ⨂ proj₂ Ps
  