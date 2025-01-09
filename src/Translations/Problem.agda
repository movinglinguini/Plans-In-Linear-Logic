open import Plans.Domain
open import Data.List hiding (_++_)

module Translations.Problem (domain : Domain) where

  open Domain domain
  open import Plans.Semantics domain

  open import Syntax.Core domain

  open import Translations.State domain
  open import Translations.Goal domain
  open import Translations.Operator domain

  -- ADJ
  open import ADJ.Core Proposition Term renaming (Context to Ctxt)

  -- Utils 
  open import Utils.WorldState domain
  
  -- Translate actions to unrestricted context
  Γₜ : List Action → Ctxt
  Γₜ [] = ∅
  Γₜ (a ∷ A) = (Γₜ A) , (translO (Γ a))
  
  private
    listToContext : ∀ { m } → List (Prop m) → Ctxt
    listToContext [] = ∅
    listToContext (x ∷ xs) = listToContext xs , x
  -- Translate initial world to linear context
  -- Requires tW, or the Total World, which is a list of all
  -- possible predicates
  Iₜ : World → World → Ctxt
  Iₜ I tW = listToContext (translS (worldToState I tW))

  Gₜ : GoalState → Prop Linear
  Gₜ G = translG G

  translP : ∀ (A : List Action) (I : World) (tW : World) (G : GoalState) → Set
  translP A I tW G = ((Γₜ A) ++ (Iₜ I tW)) ⊢ (Gₜ G ⊗ ⊤)


