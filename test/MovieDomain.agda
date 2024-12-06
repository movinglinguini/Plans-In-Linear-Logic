open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List renaming ([] to ∅; _∷_ to _,_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

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

  movieDomain : Domain
  movieDomain = record { 
    Type = Type ;
    Predicate = Predicate ;
    Action = Action ;
    Γ = Γ ;
    _≟ₚ_ = _≟ₚ_ }

  open import Translations.Operator movieDomain Object

  translatedAction : Prop Unrestricted
  translatedAction = translO (Γ rewind-movie-2)