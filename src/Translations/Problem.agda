open import Data.List
open import Plans.Domain
open import Data.List hiding (List)

import ADJ.Core
import Utils.BigTensor

module Translations.Problem (domain : Domain) where

  open Domain domain
  open import Plans.Semantics domain

  open import Translations.State domain
  open import Translations.Goal domain
  open import Translations.Operator domain

  -- ADJ
  open ADJ.Core Proposition 

  -- Utils 
  open import Utils.WorldState domain

  Γₜ : List Action → List (HProp)
  Γₜ A = map (λ α → ` (translO (Γ α))) A

  Iₜ : World → World → List (HProp)
  Iₜ I tW = map (`_) (translS (worldToState I tW))

  Gₜ : GoalState → Prop Linear
  Gₜ G = translG G

  translP : ∀ (A : List Action) (I : World) (tW : World) (G : GoalState)
          → Set
  translP A I tW G = ((Γₜ A) ++ (Iₜ I tW)) ⊢ (Gₜ G) ⊗ ⊤


