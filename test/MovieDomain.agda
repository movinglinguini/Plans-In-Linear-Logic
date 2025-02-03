open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no; does; contradiction; contraposition)
open import Data.List renaming ([] to ∅; _∷_ to _,_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Fin renaming (_≟_ to _≟f_)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; zero) renaming (_≟_ to _≟n_)

open import Plans.Domain
open import Plans.Domain.Core

module MovieDomain where
  --- Types for the domain
  data Type : Set where
    ⊤ : Type

  numberOfObjects : ℕ
  numberOfObjects = 5

  data Object : Set where
    id : ℕ → Object
    -- var : ℕ → Object

  data Predicate : Set where
    movie-rewound : Predicate
    counter-at-two-hours : Predicate
    counter-at-other-than-two-hours : Predicate
    counter-at-zero : Predicate
    have-chips : Predicate
    have-dip : Predicate
    have-pop : Predicate
    have-cheese : Predicate
    have-crackers : Predicate
    chips : Object → Predicate
    cheese : Object → Predicate
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
    effects = (⟨ + , movie-rewound ⟩) , (⟨ - , counter-at-two-hours ⟩) ,  ∅ 
    }
  Γ rewind-movie = record {
    preconditions = (⟨ + , counter-at-other-than-two-hours ⟩) , ∅ ;
    effects = (⟨ + , movie-rewound ⟩) , (⟨ - , counter-at-zero ⟩) , ∅ 
    }
  Γ reset-counter = record {
      preconditions = ∅ ;
      effects = (⟨ + , counter-at-zero ⟩) , ∅ 
    }
  Γ (get-chips c) = record { 
      preconditions = (⟨ + , chips c ⟩) , ∅ ;
      effects = (⟨ + , have-chips ⟩) , ∅ 
    }
  Γ (get-dip d) = record {
      preconditions = (⟨ + , dip d ⟩) , ∅ ;
      effects = (⟨ + , have-dip ⟩) , ∅
    }
  Γ (get-pop p) = record {
      preconditions = (⟨ + , pop p ⟩) , ∅ ;
      effects = (⟨ + , have-pop ⟩) , ∅
    }
  Γ (get-cheese c) = record {
      preconditions = (⟨ + , cheese c ⟩ , ∅) ;
      effects = (⟨ + , have-cheese ⟩) , ∅
    }
  Γ (get-crackers c) = record {
      preconditions = (⟨ + , crackers c ⟩) , ∅ ;
      effects = (⟨ + , have-crackers ⟩) , ∅
    }

  -- ########################################################
  -- Decidable Equality
  _≟ₚ_ : DecidableEquality Predicate
  movie-rewound ≟ₚ movie-rewound = yes refl
  movie-rewound ≟ₚ counter-at-two-hours = no λ()
  movie-rewound ≟ₚ counter-at-other-than-two-hours = no λ()
  movie-rewound ≟ₚ counter-at-zero = no λ()
  movie-rewound ≟ₚ have-chips = no λ()
  movie-rewound ≟ₚ have-dip = no λ()
  movie-rewound ≟ₚ have-pop = no λ()
  movie-rewound ≟ₚ have-cheese = no λ()
  movie-rewound ≟ₚ have-crackers = no λ()
  movie-rewound ≟ₚ chips x = no λ()
  movie-rewound ≟ₚ cheese x = no λ()
  movie-rewound ≟ₚ dip x = no λ()
  movie-rewound ≟ₚ pop x = no λ()
  movie-rewound ≟ₚ crackers x = no λ()
  counter-at-two-hours ≟ₚ movie-rewound = no λ()
  counter-at-two-hours ≟ₚ counter-at-two-hours = yes refl
  counter-at-two-hours ≟ₚ counter-at-other-than-two-hours = no λ()
  counter-at-two-hours ≟ₚ counter-at-zero = no λ()
  counter-at-two-hours ≟ₚ have-chips = no λ()
  counter-at-two-hours ≟ₚ have-dip = no λ()
  counter-at-two-hours ≟ₚ have-pop = no λ()
  counter-at-two-hours ≟ₚ have-cheese = no λ()
  counter-at-two-hours ≟ₚ have-crackers = no λ()
  counter-at-two-hours ≟ₚ chips x = no λ()
  counter-at-two-hours ≟ₚ cheese x = no λ()
  counter-at-two-hours ≟ₚ dip x = no λ()
  counter-at-two-hours ≟ₚ pop x = no λ()
  counter-at-two-hours ≟ₚ crackers x = no λ()
  counter-at-other-than-two-hours ≟ₚ movie-rewound = no λ()
  counter-at-other-than-two-hours ≟ₚ counter-at-two-hours = no λ()
  counter-at-other-than-two-hours ≟ₚ counter-at-other-than-two-hours = yes refl
  counter-at-other-than-two-hours ≟ₚ counter-at-zero = no λ()
  counter-at-other-than-two-hours ≟ₚ have-chips = no λ()
  counter-at-other-than-two-hours ≟ₚ have-dip = no λ()
  counter-at-other-than-two-hours ≟ₚ have-pop = no λ()
  counter-at-other-than-two-hours ≟ₚ have-cheese = no λ()
  counter-at-other-than-two-hours ≟ₚ have-crackers = no λ()
  counter-at-other-than-two-hours ≟ₚ chips x = no λ()
  counter-at-other-than-two-hours ≟ₚ cheese x = no λ()
  counter-at-other-than-two-hours ≟ₚ dip x = no λ()
  counter-at-other-than-two-hours ≟ₚ pop x = no λ()
  counter-at-other-than-two-hours ≟ₚ crackers x = no λ()
  counter-at-zero ≟ₚ movie-rewound = no λ()
  counter-at-zero ≟ₚ counter-at-two-hours = no λ()
  counter-at-zero ≟ₚ counter-at-other-than-two-hours = no λ()
  counter-at-zero ≟ₚ counter-at-zero = yes refl
  counter-at-zero ≟ₚ have-chips = no λ()
  counter-at-zero ≟ₚ have-dip = no λ()
  counter-at-zero ≟ₚ have-pop = no λ()
  counter-at-zero ≟ₚ have-cheese = no λ()
  counter-at-zero ≟ₚ have-crackers = no λ()
  counter-at-zero ≟ₚ chips x = no λ()
  counter-at-zero ≟ₚ cheese x = no λ()
  counter-at-zero ≟ₚ dip x = no λ()
  counter-at-zero ≟ₚ pop x = no λ()
  counter-at-zero ≟ₚ crackers x = no λ()
  have-chips ≟ₚ movie-rewound = no λ()
  have-chips ≟ₚ counter-at-two-hours = no λ()
  have-chips ≟ₚ counter-at-other-than-two-hours = no λ()
  have-chips ≟ₚ counter-at-zero = no λ()
  have-chips ≟ₚ have-chips = yes refl
  have-chips ≟ₚ have-dip = no λ()
  have-chips ≟ₚ have-pop = no λ()
  have-chips ≟ₚ have-cheese = no λ()
  have-chips ≟ₚ have-crackers = no λ()
  have-chips ≟ₚ chips x = no λ()
  have-chips ≟ₚ cheese x = no λ()
  have-chips ≟ₚ dip x = no λ()
  have-chips ≟ₚ pop x = no λ()
  have-chips ≟ₚ crackers x = no λ()
  have-dip ≟ₚ movie-rewound = no λ()
  have-dip ≟ₚ counter-at-two-hours = no λ()
  have-dip ≟ₚ counter-at-other-than-two-hours = no λ()
  have-dip ≟ₚ counter-at-zero = no λ()
  have-dip ≟ₚ have-chips = no λ()
  have-dip ≟ₚ have-dip = yes refl
  have-dip ≟ₚ have-pop = no λ()
  have-dip ≟ₚ have-cheese = no λ()
  have-dip ≟ₚ have-crackers = no λ()
  have-dip ≟ₚ chips x = no λ()
  have-dip ≟ₚ cheese x = no λ()
  have-dip ≟ₚ dip x = no λ()
  have-dip ≟ₚ pop x = no λ()
  have-dip ≟ₚ crackers x = no λ()
  have-pop ≟ₚ movie-rewound = no λ()
  have-pop ≟ₚ counter-at-two-hours = no λ()
  have-pop ≟ₚ counter-at-other-than-two-hours = no λ()
  have-pop ≟ₚ counter-at-zero = no λ()
  have-pop ≟ₚ have-chips = no λ()
  have-pop ≟ₚ have-dip = no λ()
  have-pop ≟ₚ have-pop = yes refl
  have-pop ≟ₚ have-cheese = no λ()
  have-pop ≟ₚ have-crackers = no λ()
  have-pop ≟ₚ chips x = no λ()
  have-pop ≟ₚ cheese x = no λ()
  have-pop ≟ₚ dip x = no λ()
  have-pop ≟ₚ pop x = no λ()
  have-pop ≟ₚ crackers x = no λ()
  have-cheese ≟ₚ movie-rewound = no λ()
  have-cheese ≟ₚ counter-at-two-hours = no λ()
  have-cheese ≟ₚ counter-at-other-than-two-hours = no λ()
  have-cheese ≟ₚ counter-at-zero = no λ()
  have-cheese ≟ₚ have-chips = no λ()
  have-cheese ≟ₚ have-dip = no λ()
  have-cheese ≟ₚ have-pop = no λ()
  have-cheese ≟ₚ have-cheese = yes refl
  have-cheese ≟ₚ have-crackers = no λ()
  have-cheese ≟ₚ chips x = no λ()
  have-cheese ≟ₚ cheese x = no λ()
  have-cheese ≟ₚ dip x = no λ()
  have-cheese ≟ₚ pop x = no λ()
  have-cheese ≟ₚ crackers x = no λ()
  have-crackers ≟ₚ movie-rewound = no λ()
  have-crackers ≟ₚ counter-at-two-hours = no λ()
  have-crackers ≟ₚ counter-at-other-than-two-hours = no λ()
  have-crackers ≟ₚ counter-at-zero = no λ()
  have-crackers ≟ₚ have-chips = no λ()
  have-crackers ≟ₚ have-dip = no λ()
  have-crackers ≟ₚ have-pop = no λ()
  have-crackers ≟ₚ have-cheese = no λ()
  have-crackers ≟ₚ have-crackers = yes refl
  have-crackers ≟ₚ chips x = no λ()
  have-crackers ≟ₚ cheese x = no λ()
  have-crackers ≟ₚ dip x = no λ()
  have-crackers ≟ₚ pop x = no λ()
  have-crackers ≟ₚ crackers x = no λ()
  chips x ≟ₚ movie-rewound = no λ()
  chips x ≟ₚ counter-at-two-hours = no λ()
  chips x ≟ₚ counter-at-other-than-two-hours = no λ()
  chips x ≟ₚ counter-at-zero = no λ()
  chips x ≟ₚ have-chips = no λ()
  chips x ≟ₚ have-dip = no λ()
  chips x ≟ₚ have-pop = no λ()
  chips x ≟ₚ have-cheese = no λ()
  chips x ≟ₚ have-crackers = no λ()
  chips (id x) ≟ₚ chips (id y) with x ≟n y
  ... | yes refl = yes refl
  ... | no ¬x=y = no (λ{ refl → ¬x=y refl})
  chips x ≟ₚ cheese x₁ = no λ()
  chips x ≟ₚ dip x₁ = no λ()
  chips x ≟ₚ pop x₁ = no λ()
  chips x ≟ₚ crackers x₁ = no λ()
  cheese x ≟ₚ movie-rewound = no λ()
  cheese x ≟ₚ counter-at-two-hours = no λ()
  cheese x ≟ₚ counter-at-other-than-two-hours = no λ()
  cheese x ≟ₚ counter-at-zero = no λ()
  cheese x ≟ₚ have-chips = no λ()
  cheese x ≟ₚ have-dip = no λ()
  cheese x ≟ₚ have-pop = no λ()
  cheese x ≟ₚ have-cheese = no λ()
  cheese x ≟ₚ have-crackers = no λ()
  cheese x ≟ₚ chips x₁ = no λ()
  cheese (id x) ≟ₚ cheese (id y) with x ≟n y
  ... | yes refl = yes refl
  ... | no ¬x=y = no (λ{ refl → ¬x=y refl})
  cheese x ≟ₚ dip x₁ = no λ()
  cheese x ≟ₚ pop x₁ = no λ()
  cheese x ≟ₚ crackers x₁ = no λ()
  dip x ≟ₚ movie-rewound = no λ()
  dip x ≟ₚ counter-at-two-hours = no λ()
  dip x ≟ₚ counter-at-other-than-two-hours = no λ()
  dip x ≟ₚ counter-at-zero = no λ()
  dip x ≟ₚ have-chips = no λ()
  dip x ≟ₚ have-dip = no λ()
  dip x ≟ₚ have-pop = no λ()
  dip x ≟ₚ have-cheese = no λ()
  dip x ≟ₚ have-crackers = no λ()
  dip x ≟ₚ chips x₁ = no λ()
  dip x ≟ₚ cheese x₁ = no λ()
  dip (id x) ≟ₚ dip (id y) with x ≟n y
  ... | yes refl = yes refl
  ... | no ¬x=y = no (λ{ refl → ¬x=y refl})
  dip x ≟ₚ pop x₁ = no λ()
  dip x ≟ₚ crackers x₁ = no λ()
  pop x ≟ₚ movie-rewound = no λ()
  pop x ≟ₚ counter-at-two-hours = no λ()
  pop x ≟ₚ counter-at-other-than-two-hours = no λ()
  pop x ≟ₚ counter-at-zero = no λ()
  pop x ≟ₚ have-chips = no λ()
  pop x ≟ₚ have-dip = no λ()
  pop x ≟ₚ have-pop = no λ()
  pop x ≟ₚ have-cheese = no λ()
  pop x ≟ₚ have-crackers = no λ()
  pop x ≟ₚ chips x₁ = no λ()
  pop x ≟ₚ cheese x₁ = no λ()
  pop x ≟ₚ dip x₁ = no λ()
  pop (id x) ≟ₚ pop (id y) with x ≟n y
  ... | yes refl = yes refl
  ... | no ¬x=y = no (λ{ refl → ¬x=y refl})
  pop x ≟ₚ crackers x₁ = no λ()
  crackers x ≟ₚ movie-rewound = no λ()
  crackers x ≟ₚ counter-at-two-hours = no λ()
  crackers x ≟ₚ counter-at-other-than-two-hours = no λ()
  crackers x ≟ₚ counter-at-zero = no λ()
  crackers x ≟ₚ have-chips = no λ()
  crackers x ≟ₚ have-dip = no λ()
  crackers x ≟ₚ have-pop = no λ()
  crackers x ≟ₚ have-cheese = no λ()
  crackers x ≟ₚ have-crackers = no λ()
  crackers x ≟ₚ chips x₁ = no λ()
  crackers x ≟ₚ cheese x₁ = no λ()
  crackers x ≟ₚ dip x₁ = no λ()
  crackers x ≟ₚ pop x₁ = no λ()
  crackers (id x) ≟ₚ crackers (id y) with x ≟n y
  ... | yes refl = yes refl
  ... | no ¬x=y = no (λ{ refl → ¬x=y refl})

  movieDomain : Domain
  movieDomain = record { 
    Type = Type ;
    Predicate = Predicate ;    
    Action = Action ;
    Γ = Γ ;
    _≟ₚ_ = _≟ₚ_ }

  open Domain movieDomain public
    hiding (Action; Predicate; Type; Γ; _≟ₚ_)

  -- Testing translation of an action definition
  open import Syntax.Core movieDomain

  open import Translations.Operator movieDomain
  open import Translations.State movieDomain 

  open import ADJ.Core movieDomain

  AD = (Γ (rewind-movie))
  tAD : Prop × Mode
  tAD = translO AD
  {-
    Output: Up[ u≥l ] ∀ . ∀ . v[counter-at-other-than-two-hours, true] ⊗ v[movie-rewond, #0] ⊗ v[counter-at-zero, #1]
                            ⊸ v[counter-at-other-than-two-hours, true] ⊗ v[movie-rewound, true] ⊗ v[counter-at-zero, true]
  -}    