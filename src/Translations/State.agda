open import Data.Nat
open import Data.List
open import Data.Vec hiding (length)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable

module Translations.State where
  open import Syntax.Core
  open import STRIPS.Problem hiding (Term)
  open import Logic.Core.Terms TermAtom
  open import Logic.Core.Props Proposition
  open import Logic.Core.Modes
  open import Translations.Condition

  variable
    𝕊 : List Condition

  translS : (𝕊 ℙ : List Condition) → Vec (Prop × Mode) (length ℙ) -- Vec Proposition (length ℙ)
  translS 𝕊 [] = []
  translS 𝕊 (x ∷ ℙ) with x ∈ᶜ? 𝕊
  ... | yes p = ⟨ ` v[ (translC x) , term "true" ] , Linear ⟩ ∷ (translS 𝕊 ℙ)
  ... | no p = ⟨ ` v[ (translC x) , term "false" ] , Linear ⟩ ∷ (translS 𝕊 ℙ)

  {- Relation between state and its translation -}
  data TranslS : ∀ (𝕊 ℙ : List Condition) → Vec (Prop × Mode) (length ℙ) → Set where
    translS/s : TranslS 𝕊 ℙ (translS 𝕊 ℙ)

  -- open Domain domain
  -- open import Plans.Semantics domain

  -- open import Syntax.Core domain
  -- open import Utils.PredMapToProposition domain
  -- open import ADJ.Core domain renaming (Context to AdjContext)

  -- open import Utils.WorldState domain

  -- variable
  --   𝕀 𝕎 : World
  --   𝕊 : State
  --   𝕊ᵗ 𝕀ᵗ : Vec (Prop × Mode) n
  --   𝕤 : PredMap
  --   𝕤ᵗ : Prop × Mode
  
  -- translS : ∀ (S : State) → Vec (Prop × Mode) (length S)
  -- translS [] = []
  -- translS (x ∷ 𝕊) = ⟨ ` (translPredmap x) , Linear ⟩ ∷ (translS 𝕊)

  -- translW : ∀ (W : World) → (Wt : World) → Vec (Prop × Mode) (length (worldToState W Wt))
  -- translW W Wt = translS (worldToState W Wt)

  -- data TranslS : ∀ ( S : State ) → Vec (Prop × Mode) (length S) → Set where
  --   Z : TranslS [] []
  --   S : TranslS 𝕊 𝕊ᵗ
  --     ---------------------- 
  --     → TranslS (𝕤 ∷ 𝕊) (⟨ ` translPredmap 𝕤 , Linear ⟩ ∷ 𝕊ᵗ)


  -- data SContext : Vec (Prop × Mode) n → AdjContext 0 n → Set where
  --   Z : SContext [] ⟨ [] , [] ⟩
  --   S : SContext 𝕊ᵗ Δ
  --     ---------------------   
  --     → SContext (𝕤ᵗ ∷ 𝕊ᵗ) (⟨ [] , 𝕤ᵗ ∷ proj₂ Δ ⟩) 