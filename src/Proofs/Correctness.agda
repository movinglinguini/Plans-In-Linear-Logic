open import Data.List using (List; _∷_; []; map; _++_)
open import Plans.Domain
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional

module Proofs.Correctness (domain : Domain) where

  open Domain domain
  open import Plans.Plan domain
  open import Plans.Semantics domain
  
  -- Syntax
  open import Syntax.Core domain

  -- Translations
  open import Translations.State domain
  open import Translations.Operator domain
  open import Translations.Goal domain

  -- ADJ
  open import ADJ.Core Proposition Term

  open import Utils.PlanToList domain
  open import Utils.WorldState domain

  lem-1 : (τ : ActionDescription) (Sₖ : State) 
          → (stateToWorld Sₖ) ∈⟨ ActionDescription.preconditions τ ⟩ 
          → (translS (ActionDescription.preconditions τ)) ⊆ translS (Sₖ)
          