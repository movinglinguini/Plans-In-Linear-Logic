open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module Utils.AllOfMode where
  open import Translations.Core.State
  open import ADJ.Core renaming (Term to AdjointTerm)

  data AllOfMode (m : Mode) : ∀ { n m } → Context n m → Set where
    all-mode/z :  ∀ { n } { T : Vec (AdjointTerm 0) n } → AllOfMode m ⟨ T , [] ⟩
    all-mode/s : ∀ { n k A } { T : Vec (AdjointTerm 0) n } { ℙ : Vec (Prop × Mode) k } 
      → AllOfMode m ⟨ T , ℙ ⟩ → (modeOf A) ≡ m
      -------------------------------
      → AllOfMode m ⟨ T , A ∷ ℙ ⟩ 
