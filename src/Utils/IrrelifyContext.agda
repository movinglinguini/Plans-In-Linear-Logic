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

  ∈≡idx : ∀ { p m Aₘ } ( Δ : Context p m )
    → ( idx : Fin m )
    → (mem : Aₘ ∈ proj₂ Δ)
    → idx ≡ ∈⇒idx Δ mem
    → Aₘ ≡ Data.Vec.lookup (proj₂ Δ) idx
  ∈≡idx { Aₘ = Aₘ } ⟨ fst , (x ∷ xs) ⟩ .(∈⇒idx { Aₘ = Aₘ } ⟨ fst , x ∷ xs ⟩ (here refl)) (here refl) refl = refl
  ∈≡idx ⟨ fst , (x ∷ xs) ⟩ .(∈⇒idx ⟨ fst , x ∷ xs ⟩ (there mem)) (there mem) refl = ∈≡idx ⟨ fst , xs ⟩ (∈⇒idx ⟨ fst , xs ⟩ mem) mem refl

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
  irrelify-allbut⇒update {i = zero} {Δ = ⟨ fst , x ∷ snd ⟩} { Δ' = Δ' } refl refl 
    = ⟨ irrelify-Only Δ' zero , N ⟩
  irrelify-allbut⇒update {i = suc i} {Δ = ⟨ fst , x ∷ snd ⟩} {Δ' = Δ'} refl refl 
    = ⟨ ⟨ [] , ⟨ (proj₁ x) , Irrelevant ⟩ ∷ [] ⟩ ++ᶜ proj₁ IH , S (proj₂ IH) ⟩
      where
        IH = irrelify-allbut⇒update { i = i } { Δ = ⟨ fst , snd ⟩ } refl refl

  -- An irrelified context is irrelevant
  irrelify-irr : ∀ { n m } ( Δ : Context n m )
    → cIrrelevant (irrelify-All Δ)
  irrelify-irr ⟨ fst , [] ⟩ = irr/n
  irrelify-irr ⟨ fst , x ∷ snd ⟩ = irr/c (irrelify-irr ⟨ fst , snd ⟩)

  -- -- A fully irrelevant context is weakenable
  irrelify-weak : ∀ { n m } ( Δ : Context n m )
    → cWeakenable (irrelify-All Δ)
  irrelify-weak ⟨ fst , [] ⟩ = weak/n
  irrelify-weak ⟨ fst , x ∷ snd ⟩ = weak/c (irrelify-weak ⟨ fst , snd ⟩ ) mweak/i

  -- A fully irrelevant context is contractable
  irrelify-contract : ∀ { n m } ( Δ : Context n m )
    → cContractable (irrelify-All Δ)
  irrelify-contract ⟨ fst , [] ⟩ = cont/n
  irrelify-contract ⟨ fst , x ∷ snd ⟩ = cont/c (irrelify-contract ⟨ fst , snd ⟩) mcontract/i

  {-
    The context attained by updating the only remaining prop to irrelevant
    after using irrelify-AllBut is all irrelevant.
  -}
  irrelify-allbut-upd-irrel-irr : ∀ { n m Aₘ i } { Δ Δ' Δ'' : Context n m }
    → (eq1 : Aₘ ≡ (Data.Vec.lookup (proj₂ Δ) i))
    → (eq2 : Δ' ≡ irrelify-AllBut Δ i)
    → (eq3 : Δ'' ≡ (proj₁ (irrelify-allbut⇒update eq1 eq2)))
    → cIrrelevant Δ''
  irrelify-allbut-upd-irrel-irr {i = zero} {⟨ fst , x ∷ snd ⟩} refl refl refl = irr/c (irrelify-irr ⟨ fst , snd ⟩)
  irrelify-allbut-upd-irrel-irr {i = suc i} {⟨ fst , x ∷ snd ⟩} refl refl refl = irr/c (irrelify-allbut-upd-irrel-irr { i = i } refl refl refl)

  -- Corollary to the above: the context attained is also weakeanable.
  irrelify-allbut-upd-irrel-weak : ∀ { n m Aₘ i } { Δ Δ' Δ'' : Context n m }
    → (eq1 : Aₘ ≡ (Data.Vec.lookup (proj₂ Δ) i))
    → (eq2 : Δ' ≡ irrelify-AllBut Δ i)
    → (eq3 : Δ'' ≡ (proj₁ (irrelify-allbut⇒update eq1 eq2)))
    → cWeakenable Δ''
  irrelify-allbut-upd-irrel-weak eq1 eq2 eq3 = cIrrelevant-to-cWeaken (irrelify-allbut-upd-irrel-irr eq1 eq2 eq3)

  -- lem : ∀ { n m Aₘ } { Δ Δ' : Context n m }
  --       → update (irrelify-All Δ) Aₘ (proj₁ Aₘ , Irrelevant) Δ'
  --       → cIrrelevant Δ'
  --     lem = {!   !}