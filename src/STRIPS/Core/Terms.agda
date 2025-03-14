open import Data.Nat hiding (_≟_)
open import Data.Fin renaming (_≟_ to _≟ᶠ_)
open import Data.Bool hiding (_≟_)
open import Data.String renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary.Decidable
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Negation
open import Data.List
open import Data.Maybe

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
  isVarᵇ (const x) = false
  isVarᵇ (var m) = true

  isConstᵇ : ∀ { s } → Term s → Bool
  isConstᵇ t = not (isVarᵇ t)

  isConst : ∀ { s } → Term s → Set
  isConst t = T (isConstᵇ t)

  isConst? : ∀ { s } ( t : Term s ) → Dec (isConst t)
  isConst? t with isConstᵇ t
  ... | false = no λ x → x
  ... | true = yes tt

  -- If two variables have the same index, then their indices must be equivalent.
  var≡var⇒i≡i : ∀ { s } { i₁ i₂ : Fin s } → var i₁ ≡ var i₂ → i₁ ≡ i₂
  var≡var⇒i≡i refl = refl

  -- If two constants have the same name, then their names must be the same.
  const≡const⇒x≡x : ∀ { s } { x₁ x₂ } → const { s } x₁ ≡ const x₂ → x₁ ≡ x₂
  const≡const⇒x≡x refl = refl

  -- Boolean equality over terms
  _≟ᵗᵇ_ : ∀ { s } → Term s → Term s → Bool
  const x ≟ᵗᵇ const x₁ = does (x ≟ˢ x₁)
  const x ≟ᵗᵇ var m = false
  var m ≟ᵗᵇ const x = false
  var m ≟ᵗᵇ var m₁ = does (m ≟ᶠ m₁)

  _≟ᵗ_ : ∀ { s } → DecidableEquality (Term s)
  const x₁ ≟ᵗ const x₂ with x₁ Data.String.≟ x₂
  ... | no ¬a = no (λ x → ¬a (const≡const⇒x≡x x))
  ... | yes a = yes (cong const a)
  const x ≟ᵗ var m = no (λ ())
  var m ≟ᵗ const x = no (λ ())
  var m₁ ≟ᵗ var m₂ with m₁ Data.Fin.≟ m₂
  ... | no ¬a = no (λ x → ¬a (var≡var⇒i≡i x))
  ... | yes a = yes (cong var a)

  _≗ᵗ_ : ∀ { s } → DecidableEquality (List (Term s))
  [] ≗ᵗ [] = yes refl
  [] ≗ᵗ (t ∷ ts₂) = no (λ ())
  (t ∷ ts₁) ≗ᵗ [] = no (λ ())
  (t₁ ∷ ts₁) ≗ᵗ (t₂ ∷ ts₂) with t₁ ≟ᵗ t₂
  ... | no ¬a = no (λ x → ¬a {!   !})
  ... | true because proof₁ = {!   !}
  
  -- Point-wise boolean equality over vectors of terms
  -- Note to self: it really sucks that we can't compare vectors of
  -- terms to avoid comparing inhabited lists with empty ones.
  _≗ᵗᵇ_ : ∀ { s } → List (Term s) → List (Term s) → Bool
  [] ≗ᵗᵇ [] = true
  [] ≗ᵗᵇ (x ∷ C₂) = false
  (x ∷ T₁) ≗ᵗᵇ [] = false
  (x ∷ T₁) ≗ᵗᵇ (x₁ ∷ T₂) = (x ≟ᵗᵇ x₁) ∧ (T₁ ≗ᵗᵇ T₂)

  -- Extracting only constants from a list of terms
  filterTerms : ∀ { s } → List (Term s) → List TermConstant
  filterTerms [] = []
  filterTerms (const x ∷ ts) = (const x) ∷ (filterTerms ts)
  filterTerms (var m ∷ ts) = filterTerms ts
    