open import Plans.Domain
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ₙ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no; does; contradiction)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Utils.PredMap.DecEquality (domain : Domain) where
  
  open Domain domain

  _≡pol?_ : DecidableEquality Polarity
  pol₁ ≡pol? pol₂ with pol₁ | pol₂
  ... | + | + = yes refl
  ... | + | - = no (λ())
  ... | - | + = no (λ ())
  ... | - | - = yes refl
  
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

  open import Data.List.Membership.DecPropositional _≟_ public using (_∈?_; _∉?_)