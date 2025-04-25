open import Data.Nat
open import Data.Vec
open import Data.List
open import Data.Fin
open import Data.Product
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any

module Utils.IrrelifyContext where
  open import Translations.Core.State
  open import ADJ.Core renaming (Term to AdjointTerm)
  open import Utils.AllOfMode

  irrelify-All : ∀ { p m } (Δ : Context p m) → Context p m
  irrelify-All ⟨ fst , [] ⟩ = ⟨ fst , [] ⟩
  irrelify-All ⟨ fst , A ∷ snd ⟩ = ⟨ [] , ⟨ proj₁ A , Irrelevant ⟩ ∷ [] ⟩ ++ᶜ irrelify-All ⟨ fst , snd ⟩

  irrelify-Only : ∀ { p m } (Δ : Context p m) → Fin m → Context p m
  irrelify-Only ⟨ fst , x ∷ snd ⟩ zero = ⟨ fst , (⟨ proj₁ x , Irrelevant ⟩ ∷ snd) ⟩
  irrelify-Only ⟨ fst , x ∷ snd ⟩ (suc idx) = ⟨ [] , x ∷ [] ⟩ ++ᶜ irrelify-Only ⟨ fst , snd ⟩ idx

  irrelify-AllBut : ∀ { p m } (Δ : Context p m) → Fin m → Context p m
  irrelify-AllBut ⟨ fst , (A ∷ As) ⟩ zero = ⟨ [] , A ∷ [] ⟩ ++ᶜ irrelify-All ⟨ fst , As ⟩
  irrelify-AllBut ⟨ fst , (B ∷ As) ⟩ (suc idx) = ⟨ [] , ⟨ proj₁ B , Irrelevant ⟩ ∷ [] ⟩ ++ᶜ irrelify-AllBut ⟨ fst , As ⟩ idx 
  
  irrelify-Vec : ∀ { p m } (Δ : Context p m)
    → List (Fin m)
    → Context p m
  irrelify-Vec Δ [] = Δ
  irrelify-Vec Δ (x ∷ xs) 
    = let Δ' = irrelify-Only Δ x
    in irrelify-Vec Δ' xs

  ∈⇒idx : ∀ { p m Aₘ } ( Δ : Context p m )
    → Aₘ ∈ proj₂ Δ
    → Fin m
  ∈⇒idx Δ (here refl) = zero
  ∈⇒idx ⟨ fst , x ∷ xs ⟩ (there mem) = suc (∈⇒idx ⟨ fst , xs ⟩ mem)

  lookup⇒∈ : ∀ { p m Aₘ i } (Δ : Context p m )
    → Aₘ ≡ Data.Vec.lookup (proj₂ Δ) i 
    → Aₘ ∈ proj₂ Δ
  lookup⇒∈ {i = zero} ⟨ fst , x ∷ snd ⟩ refl = here refl
  lookup⇒∈ {i = suc i} ⟨ fst , x ∷ snd ⟩ refl = there (lookup⇒∈ ⟨ fst , snd ⟩ refl)


  {- Properties of irrelification -}

  -- If we irrelified all but Aₘ in a context, then we still know the location
  -- of Aₘ in the new context.
  -- ∈-Δ⇒∈-IΔ : ∀ { n m i } { Aₘ : Prop × Mode } ( Δ : Context n m )
  --   → Aₘ ≡ (Data.Vec.lookup (proj₂ Δ) i)
  --   → Aₘ ∈ proj₂ (irrelify-AllBut Δ i)
  -- ∈-Δ⇒∈-IΔ {i = zero} ⟨ fst , x ∷ snd ⟩ refl = here refl
  -- ∈-Δ⇒∈-IΔ {i = suc i} ⟨ fst , x ∷ snd ⟩ refl = there (∈-Δ⇒∈-IΔ ⟨ fst , snd ⟩ refl)

  ∈-Δ⇒∈-IΔ : ∀ { n m i } { Aₘ : Prop × Mode } { Δ : Context n m }
    → Aₘ ≡ Data.Vec.lookup (proj₂ Δ) i
    → Aₘ ∈ proj₂ (irrelify-AllBut Δ i)
  ∈-Δ⇒∈-IΔ {i = zero} {Δ = ⟨ fst , x ∷ snd ⟩} refl = here refl
  ∈-Δ⇒∈-IΔ {i = suc i} {Δ = ⟨ fst , x ∷ snd ⟩} refl = there (∈-Δ⇒∈-IΔ { Δ = ⟨ fst , snd ⟩ } refl)

  irrelify-allbut⇒update : ∀ { n m Aₘ i } { Δ Δ' : Context n m }
    → Aₘ ≡ (Data.Vec.lookup (proj₂ Δ) i)
    → Δ' ≡ irrelify-AllBut Δ i
    → Σ (Context n m) (λ Δ'' → update Δ' Aₘ (proj₁ Aₘ , Irrelevant) Δ'')
  irrelify-allbut⇒update { Δ = Δ } refl refl = ∈⇒update (∈-Δ⇒∈-IΔ { Δ = Δ } refl)

  -- irrelify-allbut⇒update : ∀ { n m i Aₘ }
  --   → (Δ Δ' : Context n m)
  --   → Aₘ ≡ Data.Vec.lookup (proj₂ Δ) i
  --   → Δ' ≡ irrelify-AllBut Δ i
  --   → Σ (Context n m) (λ Δ'' → update Δ' Aₘ (proj₁ Aₘ , Irrelevant) Δ'')
  -- irrelify-allbut⇒update Δ _ refl refl = ∈⇒update (∈-Δ⇒∈-IΔ Δ refl)

  -- -- 
  -- irrelify-allbut⇒update : ∀ { n m } { k : Mode } { A : Prop } { Δ Δ' : Context n m } { mem : (A , k) ∈ proj₂ Δ }
  --   → Δ' ≡ (irrelify-AllBut Δ (A , k) mem)
  --   → Σ (Context n m) (λ Δ'' → update Δ' (A , k) (A , Irrelevant) Δ'' )
  -- irrelify-allbut⇒update {k = k} {A = A } {mem = mem} refl 
  --   = ∈⇒update (∈-Δ⇒∈-IΔ mem)

  -- -- A fully irrelevant context is weakenable
  irrelify-weak : ∀ { n m } ( Δ : Context n m )
    → cWeakenable (irrelify-All Δ)
  irrelify-weak ⟨ fst , [] ⟩ = weak/n
  irrelify-weak ⟨ fst , x ∷ snd ⟩ = weak/c (irrelify-weak ⟨ fst , snd ⟩ ) mweak/i

  -- If you irrelify the remaining prop from an irrelify-AllBut, then you have
  -- a weakenable context.
  -- irrelify-allbut-update-irr-irr :  ∀ { n m } { k : Mode } { A : Prop } { Δ Δ' : Context n m } { mem : (A , k) ∈ proj₂ Δ }
  --   → (eq : Δ' ≡ (irrelify-AllBut Δ (∈⇒idx Δ mem)))
  --   → cWeakenable (proj₁ (irrelify-allbut⇒update mem eq))
  -- irrelify-allbut-update-irr-irr {Δ = ⟨ fst , x ∷ snd ⟩} {mem = here refl} refl = weak/c (irrelify-weak ⟨ fst , snd ⟩) mweak/i
  -- irrelify-allbut-update-irr-irr {Δ = ⟨ fst , x ∷ snd ⟩} {mem = there mem} refl 
  --   = weak/c (irrelify-allbut-update-irr-irr { Δ = ⟨ fst , snd ⟩ } refl) mweak/i  