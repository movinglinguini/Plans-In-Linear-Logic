open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module Utils.IrrelifyContext where
  open import Translations.Core.State
  open import ADJ.Core renaming (Term to AdjointTerm)
  open import Utils.BigTensor Proposition
  open import Utils.AllOfMode

  {- Helper functions -}
  makeAllIrrel : ∀ { n m } → Context n m → Context n m
  makeAllIrrel ⟨ fst , snd ⟩ = ⟨ fst , irrelify snd ⟩
    where
      irrelify : ∀ { n } → Vec (Prop × Mode) n → Vec (Prop × Mode) n
      irrelify [] = []
      irrelify (x ∷ xs) = ⟨ proj₁ x , Irrelevant ⟩ ∷ irrelify xs 

  {- Properties of irrelification -}
  irrelify-is-cWeak : ∀ { n m } { IΔ Δ : Context n m } → IΔ ≡ (makeAllIrrel Δ) → cWeakenable IΔ
  irrelify-is-cWeak {Δ = ⟨ fst , [] ⟩} refl = weak/n 
  irrelify-is-cWeak {Δ = ⟨ fst , x ∷ snd ⟩} refl = weak/c (irrelify-is-cWeak refl) mweak/i

  irrelify-is-cContr : ∀ { n m } { IΔ Δ : Context n m } → IΔ ≡ (makeAllIrrel Δ) → cContractable IΔ
  irrelify-is-cContr {Δ = ⟨ fst , [] ⟩} refl = cont/n
  irrelify-is-cContr {Δ = ⟨ fst , x ∷ snd ⟩} refl = cont/c (irrelify-is-cContr refl) mcontract/i

  irrelify-merge-i : ∀ { n m } { IΔ Δ : Context n m } → IΔ ≡ (makeAllIrrel Δ) → merge IΔ IΔ IΔ
  irrelify-merge-i {Δ = ⟨ fst , [] ⟩} refl = mg/n 
  irrelify-merge-i {Δ = ⟨ fst , x ∷ snd ⟩} refl = mg/c (irrelify-merge-i refl) i∙i

  irrelify-merge-l : ∀ { n m } { IΔ Δ : Context n m } → IΔ ≡ (makeAllIrrel Δ) → AllOfMode Linear Δ → merge IΔ Δ Δ
  irrelify-merge-l refl all-mode/z = mg/n 
  irrelify-merge-l refl (all-mode/s {A = ⟨ fst , Linear ⟩} lin x) = mg/c (irrelify-merge-l refl lin) i∙l 