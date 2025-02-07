open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)

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
