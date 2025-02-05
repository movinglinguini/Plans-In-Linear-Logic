open import Data.Nat
open import Data.List
open import Data.Vec hiding (length)
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Plans.Domain

{--
For pretty printing
-}
open import Text.Pretty 80
open import Data.Nat.Show

module Translations.State (domain : Domain) where
  open Domain domain
  open import Plans.Semantics domain

  open import Syntax.Core domain
  open import Utils.PredMapToProposition domain
  open import ADJ.Core domain renaming (Context to AdjContext)

  open import Utils.WorldState domain

  variable
    𝕀 𝕎 : World
    𝕊 : State
    𝕊ᵗ 𝕀ᵗ : Vec (Prop × Mode) n
    𝕤 : PredMap
    𝕤ᵗ : Prop × Mode
  
  translS : ∀ (S : State) → Vec (Prop × Mode) (length S)
  translS [] = []
  translS (x ∷ 𝕊) = ⟨ ` (translPredmap x) , Linear ⟩ ∷ (translS 𝕊)

  translW : ∀ (W : World) → (Wt : World) → Vec (Prop × Mode) (length (worldToState W Wt))
  translW W Wt = translS (worldToState W Wt)

  data TranslS : ∀ ( S : State ) → Vec (Prop × Mode) (length S) → Set where
    Z : TranslS [] []
    S : TranslS 𝕊 𝕊ᵗ
      ---------------------- 
      → TranslS (𝕤 ∷ 𝕊) (⟨ ` translPredmap 𝕤 , Linear ⟩ ∷ 𝕊ᵗ)


  data SContext : Vec (Prop × Mode) n → AdjContext 0 n → Set where
    Z : SContext [] ⟨ [] , [] ⟩
    S : SContext 𝕊ᵗ Δ
      --------------------- 
      → SContext (𝕤ᵗ ∷ 𝕊ᵗ) (⟨ [] , 𝕤ᵗ ∷ proj₂ Δ ⟩) 