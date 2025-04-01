open import Data.List
open import Data.Vec hiding (foldr)
open import Data.Bool
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Relation.Nullary.Negation

module STRIPS.Core.Sat where
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Goals

  {- Satisfaction of conditions -}

  -- Boolean satisfaction: a condition satisfies a pair of lists of conditions if
  -- 1. all of the left part of the pair (the positive side) can be found in the condition
  -- 2. none of the right part of the pair (the negative side) can be found in the condition
  satᵇ : List GroundCondition → (List (Condition 0)) × (List (Condition 0)) → Bool
  satᵇ C ⟨ G⁺ , G⁻ ⟩ = (allIn C G⁺) ∧ (noneIn C G⁻)
    where
      allIn : List (Condition 0) → List (Condition 0) → Bool
      allIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (x ∈ᶜᵇ ℂ₁)) true ℂ₂

      noneIn : List (Condition 0) → List (Condition 0) → Bool
      noneIn ℂ₁ ℂ₂ = foldr (λ x acc → acc ∧ (not (x ∈ᶜᵇ ℂ₁))) true ℂ₂ 


  -- Propositional satisfaction: Similar to above, but we use propositional list membership.
  -- sat : List GroundCondition → (List (Condition 0)) × (List (Condition 0)) → Set
  -- sat 𝕊 𝔾 = T (satᵇ 𝕊 𝔾)

  -- sat′ : List GroundCondition → (List (Condition 0)) × (List (Condition 0)) → Set
  -- sat′ S G = (∀ g → g ∈ (proj₁ G) → g ∈ S) × (∀ g → g ∈ (proj₂ G) → g ∉ S)

  sat-Condition : List GroundCondition → (GroundCondition × Bool) → Set
  sat-Condition S ⟨ c , false ⟩ = c ∉ S
  sat-Condition S ⟨ c , true ⟩ = c ∈ S 

  data sat : List GroundCondition → List (GroundCondition × Bool) → Set where
    sat/z : ∀ { S } → sat S []

    sat/s/neg : ∀ { S gs c } 
      → sat S gs    →   c ∉ S
      → sat S (⟨ c , false ⟩ ∷ gs) 

    sat/s/pos : ∀ { S gs c }
      → sat S gs    →   c ∈ S
      → sat S (⟨ c , true ⟩ ∷ gs)

  {-
    Properties of sat
  -}
  satg∷G⇒satG : ∀ { g G S } → sat S (g ∷ G) → sat S G
  satg∷G⇒satG (sat/s/neg sat₁ x) = sat₁
  satg∷G⇒satG (sat/s/pos sat₁ x) = sat₁

  sat⇒∉ : ∀ { c gs S } → sat S (⟨ c , false ⟩ ∷ gs) → c ∉ S
  sat⇒∉ (sat/s/neg s x) = x

  sat⇒∈ : ∀ { c gs S } → sat S (⟨ c , true ⟩ ∷ gs) → c ∈ S
  sat⇒∈ (sat/s/pos s x) = x

  ∈⇒not-sat : ∀ { c gs S } → c ∈ S → ¬ (sat S (⟨ c , false ⟩ ∷ gs))
  ∈⇒not-sat mem = λ x → contraposition sat⇒∉ (λ z → z mem) x

  ∉⇒not-sat : ∀ { c gs S } → c ∉ S → ¬ (sat S (⟨ c , true ⟩ ∷ gs))
  ∉⇒not-sat notmem = λ x → contraposition sat⇒∈ notmem x
  
  -- Decidable satisfaction
  open import Data.List.Membership.DecPropositional { A = GroundCondition } (_≟ᶜ_)
  sat? : (S : List GroundCondition) → (gs : List (GroundCondition × Bool)) → Dec(sat S gs)
  sat? S [] = yes sat/z
  sat? S (⟨ c , false ⟩ ∷ gs) with c ∈? S
  ... | no ¬a with sat? S gs
  ...   |   no ¬b = no (λ x → ¬b (satg∷G⇒satG x))
  ...   |   yes b = yes (sat/s/neg b ¬a)
  sat? S (⟨ c , false ⟩ ∷ gs) | yes a = no (∈⇒not-sat a)
  sat? S (⟨ c , true ⟩ ∷ gs) with c ∈? S
  ... | no ¬a = no (∉⇒not-sat ¬a)
  ... | yes a with sat? S gs
  ...   | no ¬b = no λ x → ¬b (satg∷G⇒satG x)
  ...   | yes b = yes (sat/s/pos b a) 

  -- Testing out satisfaction
  private
    state : List GroundCondition
    state = (record { label = "cond-1" ; terms = [] }) ∷ []

    goal1 : GroundCondition × Bool
    goal1 = ⟨ record { label = "cond-1" ; terms = [] } , true ⟩

    goal2 : GroundCondition × Bool
    goal2 = ⟨ record { label = "cond-2" ; terms = [] } , false ⟩

    goal2-neg : (proj₁ goal2) Data.List.Membership.Propositional.∉ state
    goal2-neg with (proj₁ goal2) ∈? state
    ... | no ¬a = ¬a
    ... | yes (here ())
    ... | yes (there ()) 

    _ : sat state (goal1 ∷ goal2 ∷ [])
    _ = sat/s/pos (sat/s/neg sat/z goal2-neg) (here refl)
