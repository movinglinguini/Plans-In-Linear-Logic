open import Plans.Domain
open import Data.List hiding (_++_)
open import Data.Vec hiding (length)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Translations.Problem (domain : Domain) where

  open Domain domain
  open import Plans.Semantics domain

  open import Syntax.Core domain

  open import Translations.State domain
  open import Translations.Goal domain
  open import Translations.Operator domain

  -- ADJ
  open import ADJ.Core domain renaming (Context to Ctxt)

  -- Utils 
  open import Utils.WorldState domain
  
  -- Translate actions to unrestricted context
  Γₜ : (A : List Action) → Ctxt 2 (length A)
  Γₜ [] = ⟨ (term true ∷ (term false ∷ Vec.[])) , Vec.[] ⟩
  Γₜ (x ∷ A) = ⟨ term true ∷ (term false ∷ []) , (translO (Γ x) ∷ proj₂ (Γₜ A)) ⟩

  -- Translate the world state into a linear context
  Δₜ : ∀ ( I W : World ) → Ctxt 0 (length (worldToState I W))
  Δₜ I W = ⟨ [] , translS (worldToState I W) ⟩ 

  translP : ∀ (A : List Action) (𝕀 : World) (𝕎 : World) (𝔾 : GoalState) → Set
  translP A 𝕀 𝕎 𝔾 = (Γₜ A ++ᶜ Δₜ 𝕀 𝕎) ⊢ⁱ ⟨ translG 𝔾 ⊗ ⊤ , Linear ⟩
  
 
 