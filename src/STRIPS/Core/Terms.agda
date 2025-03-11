open import Data.Nat hiding (_≟_)
open import Data.Fin renaming (_≟_ to _≟ᶠ_)
open import Data.Bool hiding (_≟_)
open import Data.String renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Negation
open import Data.List

module STRIPS.Core.Terms where
  TermAtom = String

  -- A Term n is a term that's well-formed in a scope with n variables
  data Term : (Scope : ℕ) → Set where 
    const : ∀ { n } → TermAtom → Term n
    var : ∀ { n } ( m : Fin n ) → Term n

  -- A constant term is just a term at 0 scope
  TermConstant = Term 0

  {- Operations on terms -}

  -- Identifying terms as variables or constants
  isVarᵇ : ∀ { s } → Term s → Bool
  isVarᵇ (const x) = true
  isVarᵇ (var m) = false

  isConstᵇ : ∀ { s } → Term s → Bool
  isConstᵇ t = not (isVarᵇ t)

  isConst : ∀ { s } → Term s → Set
  isConst t = T (isConstᵇ t)

  isConst? : ∀ { s } ( t : Term s ) → Dec (isConst t)
  isConst? t with isConstᵇ t
  ... | false = no λ x → x
  ... | true = yes tt

  -- Boolean equality over terms
  _≟ᵗᵇ_ : ∀ { s } → Term s → Term s → Bool
  const x ≟ᵗᵇ const x₁ = does (x ≟ˢ x₁)
  const x ≟ᵗᵇ var m = false
  var m ≟ᵗᵇ const x = false
  var m ≟ᵗᵇ var m₁ = does (m ≟ᶠ m₁)

  -- Point-wise boolean equality over vectors of terms
  -- Note to self: it really sucks that we can't compare vectors of
  -- terms to avoid comparing inhabited lists with empty ones.
  _≗ᵗ_ : ∀ { s } → List (Term s) → List (Term s) → Bool
  [] ≗ᵗ [] = true
  [] ≗ᵗ (x ∷ C₂) = false
  (x ∷ T₁) ≗ᵗ [] = false
  (x ∷ T₁) ≗ᵗ (x₁ ∷ T₂) = (x ≟ᵗᵇ x₁) ∧ (T₁ ≗ᵗ T₂)

  -- Extracting only constants from a list of terms
  filterTerms : ∀ { s } → List (Term s) → List TermConstant
  filterTerms [] = []
  filterTerms (const x ∷ ts) = (const x) ∷ (filterTerms ts)
  filterTerms (var m ∷ ts) = filterTerms ts
 