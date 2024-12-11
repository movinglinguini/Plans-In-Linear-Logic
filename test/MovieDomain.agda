open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no; does; contradiction; contraposition)
open import Data.List renaming ([] to ∅; _∷_ to _,_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (zero)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

open import Plans.Domain
open import Plans.Domain.Core

module MovieDomain where
  --- Types for the domain
  data Type : Set where
    ⊤ : Type

  data Object : Set where
    x : Object

  data Predicate : Set where
    movie-rewound : Predicate
    counter-at-two-hours : Predicate
    counter-at-other-than-two-hours : Predicate
    counter-at-zero : Predicate
    have-chips : Predicate
    have-dip : Predicate
    have-pop : Predicate
    have-cheese : Predicate
    chips : Object → Predicate
    dip : Object → Predicate
    pop : Object → Predicate
    crackers : Object → Predicate

  data Action : Set where
    rewind-movie-2 : Action
    rewind-movie : Action
    reset-counter : Action
    get-chips : Object → Action
    get-dip : Object → Action
    get-pop : Object → Action
    get-cheese : Object → Action
    get-crackers : Object → Action

  Γ : Action → ActionDescription Type Action Predicate
  Γ rewind-movie-2 = record { 
    preconditions = (⟨ + , counter-at-two-hours ⟩) , ∅ ;
    effects = (⟨ + , movie-rewound ⟩) , ∅ 
    }
  Γ rewind-movie = {!   !}
  Γ reset-counter = {!   !}
  Γ (get-chips x₁) = {!   !}
  Γ (get-dip x₁) = {!   !}
  Γ (get-pop x₁) = {!   !}
  Γ (get-cheese x₁) = {!   !}
  Γ (get-crackers x₁) = {!   !}

  -- ########################################################
  -- Decidable Equality
  _≟ₚ_ : DecidableEquality Predicate
  p₁ ≟ₚ p₂ with p₁ | p₂
  ... | movie-rewound | movie-rewound = yes refl
  ... | movie-rewound | counter-at-two-hours = no (λ ())
  ... | movie-rewound | counter-at-other-than-two-hours = no (λ ())
  ... | movie-rewound | counter-at-zero = no (λ ())
  ... | movie-rewound | have-chips = no (λ ())
  ... | movie-rewound | have-dip = no (λ ())
  ... | movie-rewound | have-pop = no (λ ())
  ... | movie-rewound | have-cheese = no (λ ())
  ... | movie-rewound | chips x₁ = no (λ ())
  ... | movie-rewound | dip x₁ = no (λ ())
  ... | movie-rewound | pop x₁ = no (λ ())
  ... | movie-rewound | crackers x₁ = no (λ ())
  ... | counter-at-two-hours | movie-rewound = no (λ ())
  ... | counter-at-two-hours | counter-at-two-hours = yes refl
  ... | counter-at-two-hours | counter-at-other-than-two-hours = no (λ ())
  ... | counter-at-two-hours | counter-at-zero = no (λ ())
  ... | counter-at-two-hours | have-chips = no (λ ())
  ... | counter-at-two-hours | have-dip = no (λ ())
  ... | counter-at-two-hours | have-pop = no (λ ())
  ... | counter-at-two-hours | have-cheese = no (λ ())
  ... | counter-at-two-hours | chips x₁ = no (λ ())
  ... | counter-at-two-hours | dip x₁ = no (λ ())
  ... | counter-at-two-hours | pop x₁ = no (λ ())
  ... | counter-at-two-hours | crackers x₁ = no (λ ())
  ... | counter-at-other-than-two-hours | movie-rewound = no (λ ())
  ... | counter-at-other-than-two-hours | counter-at-two-hours = no (λ ())
  ... | counter-at-other-than-two-hours | counter-at-other-than-two-hours = yes refl
  ... | counter-at-other-than-two-hours | counter-at-zero = no (λ ())
  ... | counter-at-other-than-two-hours | have-chips = no (λ ())
  ... | counter-at-other-than-two-hours | have-dip = no (λ ())
  ... | counter-at-other-than-two-hours | have-pop = no (λ ())
  ... | counter-at-other-than-two-hours | have-cheese = no (λ ())
  ... | counter-at-other-than-two-hours | chips x₁ = no (λ ())
  ... | counter-at-other-than-two-hours | dip x₁ = no (λ ())
  ... | counter-at-other-than-two-hours | pop x₁ = no (λ ())
  ... | counter-at-other-than-two-hours | crackers x₁ = no (λ ())
  ... | counter-at-zero | movie-rewound = no (λ ())
  ... | counter-at-zero | counter-at-two-hours = no (λ ())
  ... | counter-at-zero | counter-at-other-than-two-hours = no (λ ())
  ... | counter-at-zero | counter-at-zero = yes refl
  ... | counter-at-zero | have-chips = no (λ ())
  ... | counter-at-zero | have-dip = no (λ ())
  ... | counter-at-zero | have-pop = no (λ ())
  ... | counter-at-zero | have-cheese = no (λ ())
  ... | counter-at-zero | chips x₁ = no (λ ())
  ... | counter-at-zero | dip x₁ = no (λ ())
  ... | counter-at-zero | pop x₁ = no (λ ())
  ... | counter-at-zero | crackers x₁ = no (λ ())
  ... | have-chips | b = {!   !}
  ... | have-dip | b = {!   !}
  ... | have-pop | b = {!   !}
  ... | have-cheese | b = {!   !}
  ... | chips x₁ | b = {!   !}
  ... | dip x₁ | b = {!   !}
  ... | pop x₁ | b = {!   !}
  ... | crackers x₁ | b = {!   !}

  movieDomain : Domain
  movieDomain = record { 
    Type = Type ;
    Predicate = Predicate ;    
    Action = Action ;
    Γ = Γ ;
    _≟ₚ_ = _≟ₚ_ }

  -- Testing translation of an action definition
  open import Translations.Operator movieDomain Object

  AD = (Γ rewind-movie-2)
  condAD = cond AD

  translatedAction : Prop Unrestricted
  translatedAction = translO AD condAD 𝟙 𝟙 zero  
  {-
    Output: Up[ u≥l ] ⟨ polvar 0 , movie-rewound ⟩ ⊗ ⟨ + counter-at-two-hours ⟩ ⊗ 𝟙 
                    ⊸ ⟨ + , movie-rewound ⟩ ⊗ ⟨ + , counter-at-two-hours ⟩ ⊗ 𝟙 
  -}  