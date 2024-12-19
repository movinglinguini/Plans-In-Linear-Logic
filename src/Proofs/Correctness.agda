open import Data.List using (List; _∷_; []; map; _++_)
open import Plans.Domain

module Proofs.Correctness (domain : Domain) where

  open Domain domain
  open import Plans.Plan domain
  open import Plans.Semantics domain
  
  -- Translations
  open import Translations.State domain
  open import Translations.Operator domain
  open import Translations.Goal domain

  -- ADJ
  open import ADJ.Core Proposition

  open import Utils.WorldState domain using (worldToState)

  ValidPlan = ∀ ( P : Plan ) ( I : World ) ( G : GoalState ) → Γ ⊢ P ∶ I ↝ G


  

  completeness : ∀ (A : List Action) (I : World) (tW : World) (G : GoalState) 
                    → {!   !} 
                    → {!  !}

  -- completeness P I G = {!   !} 
