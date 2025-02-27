open import Data.List
open import Data.Maybe
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable


module STRIPS.Core.Plans where
  open import STRIPS.Core.Operators
  open import STRIPS.Core.Goals
  open import STRIPS.Core.Conditions
  open import STRIPS.Core.Common
  
  Plan = List GroundOperator

  private 
    variable
      Τ : Plan
      𝕀 : List (Condition 0)
      𝔾 : Goal
      τ : GroundOperator
  
  {- Well-typed plan -}
  data Solves : List (Condition 0) → Plan → Goal → Set where
    solves/z : sat 𝕀 ⟨ Goal.pos 𝔾 , Goal.neg 𝔾 ⟩
      → Solves 𝕀 [] 𝔾

    solves/s : Solves (update τ 𝕀) Τ 𝔾
      → sat 𝕀 ⟨ GroundOperator.posPre τ , GroundOperator.negPre τ ⟩
      → Solves 𝕀 (τ ∷ Τ) 𝔾 

