open import Data.String
open import Data.List 
open import Data.Vec

module Translations.Core.Term where
  open import STRIPS.Problem renaming (Term to STRIPSTerm)
  open import Logic.Core.Terms TermAtom renaming (Term to ADJTerm)

  translT : STRIPSTerm → ADJTerm 
  translT (term x) = term x
  translT (var x) = var x

  -- Relation between a strips term and its translation into an adjoint term
  data TranslT : STRIPSTerm → ADJTerm → Set where
    translT/z : ∀ { t : STRIPSTerm } → TranslT t (translT t)

  data TranslTs : ∀ ( T : List STRIPSTerm ) → Vec ADJTerm (Data.List.length T) → Set where  
    translTs/z : ∀ { T : List STRIPSTerm } { Tᵗ : Vec ADJTerm (Data.List.length T) }
      { t : STRIPSTerm } { tᵗ : ADJTerm }
      →  TranslTs T Tᵗ → TranslT t tᵗ
      -----------------------------------
      → TranslTs (t ∷ T) (tᵗ ∷ Tᵗ)
