open import Data.List
open import Data.Maybe
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable


module STRIPS.Core.Plans where
  open import STRIPS.Core.Operators
  open import STRIPS.Core.Goals
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Common
  
  Plan = List Operator

  private 
    variable
      Τ : Plan
      𝕀 : List Condition
      𝔾 : Goal
  
  {- Well-typed plan -}
  data Solves : List Condition → Plan → Goal → Set where
    solves/z : sat 𝕀 ⟨ Goal.pos 𝔾 , Goal.neg 𝔾 ⟩
      → Solves 𝕀 [] 𝔾

    solves/s : Solves (update 𝕀 τ) Τ 𝔾
      → sat 𝕀 ⟨ τ ⁺ , τ ⁻ ⟩
      → Solves 𝕀 (τ ∷ Τ) 𝔾 

  solver : ∀ ( 𝕀 : List Condition ) ( P : Plan ) ( 𝔾 : Goal ) → Maybe (Solves 𝕀 P 𝔾)
  solver 𝕀 [] 𝔾 with sat? 𝕀 ⟨ Goal.pos 𝔾 , Goal.neg 𝔾 ⟩
  ... | yes p = just (solves/z p)
  ... | no ¬p = nothing
  solver 𝕀 (τ ∷ P) 𝔾 with sat? 𝕀 ⟨ τ ⁺ , τ ⁻ ⟩
  ... | no ¬p = nothing
  ... | yes p with solver (update 𝕀 τ) P 𝔾
  ... | nothing = nothing
  ... | just x = just (solves/s x p)
