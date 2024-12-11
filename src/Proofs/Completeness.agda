open import Data.List
open import Plans.Domain

module Proofs.Completeness (domain : Domain) (U : Set) (T : Set) where

  open Domain domain
  open import Plans.Plan domain
  open import Plans.Semantics domain
  open import Plans.PredMap.Properties domain
  
  open import ADJ.Core U T
  open import Translations.Problem domain T

  open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)
  --- Satisfaction
  data sat⟨_,_⟩ : State → State → Set where
    sat : ∀ { W S }
      → W ⊆ S
      -------------------
      → sat⟨ W , S ⟩

  -- Plan as solution




  -- completeness : ∀ (P : Plan) (I : State) (G : GoalState) → Γ ⊢ P ∶ I ↝ G → goalJgmt
  -- completeness P I G = {!   !} 
