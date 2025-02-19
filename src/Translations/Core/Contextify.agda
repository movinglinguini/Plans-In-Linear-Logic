open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Translations.Core.Contextify where
  -- Relation between a vector of moded propositions and its interpretation
  -- as a partial context for a sequent
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.State
  open import Logic.Core.Terms TermAtom
  open import Logic.Core.Props Proposition
  open import Logic.Core.Modes
  open import Logic.Core.Contexts Proposition TermAtom
  
  data Contextify : ∀ { n m } → Vec Term n → Vec (Prop × Mode) m → Context n m → Set where
    contextify/n : ∀ { n } → (T : Vec Term n) 
      → Contextify T [] ⟨ T , [] ⟩
    
    contextify/s : ∀ { n m } → (T : Vec Term n) → (As Δ : Vec (Prop × Mode) m) → (A : Prop × Mode)
      → Contextify T As ⟨ T , Δ ⟩
      → Contextify T (A ∷ As) ⟨ T , A ∷ Δ ⟩