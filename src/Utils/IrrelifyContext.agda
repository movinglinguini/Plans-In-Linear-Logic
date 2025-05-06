open import Data.Nat
open import Data.Vec
open import Data.List hiding (merge)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_)
open import Data.Fin
open import Data.Product
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality 
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵛ_)
open import Data.Vec.Relation.Unary.Any
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All.Properties
open import Relation.Nullary.Negation using (contradiction; contraposition; ¬_)
open import Relation.Nullary hiding (Irrelevant)

module Utils.IrrelifyContext where
  open import Translations.Core.State
  open import ADJ.Core renaming (Term to AdjointTerm)
  open import Utils.AllOfMode

  data LinOrIrr : ∀ { n m } → Context n m → Set where
    lin/irr/z : ∀ { n } { ts : Vec (AdjointTerm 0) n }
      → LinOrIrr ⟨ ts , [] ⟩
    lin/irr/s-1 : ∀ { n m A } { Δ : Context n m }
      → LinOrIrr Δ
      → LinOrIrr ⟨ proj₁ Δ , (⟨ A , Linear ⟩ ∷ proj₂ Δ) ⟩
    lin/irr/s-2 : ∀ { n m A } { Δ : Context n m }
      → LinOrIrr Δ
      → LinOrIrr ⟨ proj₁ Δ , (⟨ A , Irrelevant ⟩ ∷ proj₂ Δ) ⟩

  {-
    Properties of LinOrIrr
  -}

  -- Linear contexts are LinOrIrr contexts
  lin-to-lin/irr : ∀ { n m } {Δ : Context n m}
    → cLinear Δ
    → LinOrIrr Δ
  lin-to-lin/irr lin/n = lin/irr/z
  lin-to-lin/irr (lin/c lin) = lin/irr/s-1 (lin-to-lin/irr lin)

  -- Irrelevant contexts are LinOrIrr contexts
  irr-to-lin/irr : ∀ { n m } { Δ : Context n m }
    → cIrrelevant Δ
    → LinOrIrr Δ
  irr-to-lin/irr irr/n = lin/irr/z
  irr-to-lin/irr (irr/c irr) = lin/irr/s-2 (irr-to-lin/irr irr)

  -- Fully Irrelevant contexts are the left identity of LinOrIrr contexts in a merge
  -- if they are comparable.
  irrel-lin/irr-merge-id-left : ∀ { n m } { Δ₁ Δ₂ : Context n m }
    → LinOrIrr Δ₁
    → cIrrelevant Δ₂
    → Comparable Δ₁ Δ₂
    → merge Δ₂ Δ₁ Δ₁
  irrel-lin/irr-merge-id-left lin/irr irr comp/z = mg/n
  irrel-lin/irr-merge-id-left (lin/irr/s-1 lin/irr) (irr/c irr) (comp/s comp) = mg/c (irrel-lin/irr-merge-id-left lin/irr irr comp) i∙l
  irrel-lin/irr-merge-id-left (lin/irr/s-2 lin/irr) (irr/c irr) (comp/s comp) = mg/c (irrel-lin/irr-merge-id-left lin/irr irr comp) i∙i

  private
    irrelify-All-prop : ∀ { m } → Vec (Prop × Mode) m → Vec (Prop × Mode) m
    irrelify-All-prop [] = []
    irrelify-All-prop (p ∷ ps) = ⟨ (proj₁ p) , Irrelevant ⟩ ∷ (irrelify-All-prop ps)

  irrelify-All : ∀ { p m } (Δ : Context p m) → Context p m
  irrelify-All ⟨ fst , snd ⟩ = ⟨ fst , irrelify-All-prop snd ⟩

  {-
    Properties of irrelify-All
  -}
  -- When you irrelify all of a context, then the result is comparable to the original
  irrelify-all-comp : ∀ { m n } (Δ : Context n m)
    → Comparable Δ (irrelify-All Δ)
  irrelify-all-comp ⟨ fst , [] ⟩ = comp/z
  irrelify-all-comp ⟨ fst , x ∷ snd ⟩ = comp/s (irrelify-all-comp ⟨ fst , snd ⟩)

  private
    irrelify-Only-prop : ∀ { m } → Vec (Prop × Mode) m → Fin m → Vec (Prop × Mode) m
    irrelify-Only-prop (p ∷ ps) zero = ⟨ proj₁ p , Irrelevant ⟩ ∷ ps
    irrelify-Only-prop (p ∷ ps) (suc idx) = p ∷ irrelify-Only-prop ps idx

  irrelify-Only : ∀ { p m } (Δ : Context p m) → Fin m → Context p m
  irrelify-Only ⟨ fst , snd ⟩ idx = ⟨ fst , irrelify-Only-prop snd idx ⟩

  {- Properties of irrelify-Only -}
  -- If we irrelify a prop in a linear context, then the result is
  -- a context that is part linear, part irrelevant.
  irrel-only-lin/irr-1 : ∀ { n m } { Δ : Context n m }
    → (i : Fin m)
    → cLinear Δ
    → LinOrIrr (irrelify-Only Δ i)
  irrel-only-lin/irr-1 zero (lin/c lin) = lin/irr/s-2 (lin-to-lin/irr lin)
  irrel-only-lin/irr-1 (suc i) (lin/c lin) = lin/irr/s-1 (irrel-only-lin/irr-1 i lin)

  -- If we irrelify a prop in a context that is part linear, part irrelevant, then
  -- the result is a context that is part linear, part irrelevant.
  irrel-only-lin/irr-2 : ∀ { n m } { Δ : Context n m }
    → (i : Fin m)
    → LinOrIrr Δ
    → LinOrIrr (irrelify-Only Δ i)
  irrel-only-lin/irr-2 zero (lin/irr/s-1 lin/irr) = lin/irr/s-2 lin/irr
  irrel-only-lin/irr-2 zero (lin/irr/s-2 lin/irr) = lin/irr/s-2 lin/irr
  irrel-only-lin/irr-2 (suc i) (lin/irr/s-1 lin/irr) = lin/irr/s-1 (irrel-only-lin/irr-2 i lin/irr)
  irrel-only-lin/irr-2 (suc i) (lin/irr/s-2 lin/irr) = lin/irr/s-2 (irrel-only-lin/irr-2 i lin/irr)

  -- If we irrelify a prop in a context, the result is comparable to the original.
  irrel-only-comp : ∀ { n m } ( Δ : Context n m )
    → (i : Fin m)
    → Comparable Δ (irrelify-Only Δ i)
  irrel-only-comp ⟨ fst , x ∷ snd ⟩ zero = comp/s comparable-id
  irrel-only-comp ⟨ fst , x ∷ snd ⟩ (suc i) = comp/s (irrel-only-comp ⟨ fst , snd ⟩ i)


  {- Irrelifying all but one prop -}
  private
    irrelify-AllBut-prop : ∀ { m } → Vec (Prop × Mode) m → Fin m → Vec (Prop × Mode) m
    irrelify-AllBut-prop (x ∷ xs) zero = x ∷ irrelify-All-prop xs
    irrelify-AllBut-prop (x ∷ xs) (suc idx) = ⟨ proj₁ x , Irrelevant ⟩ ∷ irrelify-AllBut-prop xs idx

  irrelify-AllBut : ∀ { p m } (Δ : Context p m) → Fin m → Context p m
  irrelify-AllBut ⟨ fst , As ⟩ idx = ⟨ fst , irrelify-AllBut-prop As idx ⟩

  -- Irrelify by a list of indices
  irrelify-List : ∀ { p m } (Δ : Context p m)
    → List (Fin m)
    → Context p m
  irrelify-List Δ [] = Δ
  irrelify-List Δ (x ∷ xs) 
    = let Δ' = irrelify-Only Δ x
    in irrelify-List Δ' xs

  -- Property of irrelifying by a list: we can irrelify in such a way that
  -- preserves the linearity/irrelevancy of the original context.
  irrelify-List-lin/irr : ∀ { n m } (Δ : Context n m)
    → List (Fin m)
    → LinOrIrr Δ
    → Σ (Context n m) (λ Δ' → (LinOrIrr Δ' × Comparable Δ Δ'))
  irrelify-List-lin/irr Δ [] lin/irr = ⟨ Δ , ⟨ lin/irr , comparable-id ⟩ ⟩
  irrelify-List-lin/irr Δ (x ∷ lst) lin/irr 
    = let Δ' = irrelify-List-lin/irr Δ lst lin/irr
      in let Δ'' = irrelify-Only (proj₁ Δ') x
      in let Δ''-comp = irrel-only-comp (proj₁ Δ') x
      in let Δ''-lin/irr = irrel-only-lin/irr-2 x (proj₁ (proj₂ Δ'))
      in ⟨ Δ'' , ⟨ Δ''-lin/irr , 
                  comparable-trans (proj₂ (proj₂ Δ')) Δ''-comp ⟩ ⟩
                  
  -- Extension of the above function, but starting with a fully linear context.
  irrelify-List-lin : ∀ { n m } (Δ : Context n m)
    → List (Fin m)
    → cLinear Δ
    → Σ (Context n m) (λ Δ' → (LinOrIrr Δ' × Comparable Δ Δ'))
  irrelify-List-lin Δ lst lin = irrelify-List-lin/irr Δ lst (lin-to-lin/irr lin)

  irrelify-list-mem : ∀ { n m idx Aₗ } { Δ : Context n m }
    → (lin : cLinear Δ)
    → (lst : List (Fin m))
    → Aₗ ≡ Data.Vec.lookup (proj₂ (proj₁ (irrelify-List-lin Δ lst lin))) idx
    → proj₂ Aₗ ≡ Irrelevant
    → idx ∈ˡ lst
  irrelify-list-mem {idx = zero} {Δ = ⟨ fst , .(⟨ _ , Linear ⟩) ∷ snd ⟩} (lin/c lin) [] refl ()
  irrelify-list-mem {idx = zero} lin (zero ∷ lst) refl eq2 = here refl
  irrelify-list-mem {idx = zero} {Δ = Δ} lin (suc x ∷ lst) eq1 refl = there (irrelify-list-mem lin lst refl {!   !})
  irrelify-list-mem {idx = suc idx} {Δ = ⟨ fst , .(⟨ _ , Linear ⟩ ∷ _) ⟩} (lin/c lin) [] refl eq2 = contradiction eq2 (λ x → {!   !})
  irrelify-list-mem {idx = suc idx} lin (zero ∷ lst) refl eq2 = there (irrelify-list-mem lin lst refl {!   !})
  irrelify-list-mem {idx = suc idx} lin (suc x ∷ lst) refl eq2 = {!   !}

  -- Let's say we've irrelified propositions from a unique list in a linea context. Then any proposition
  -- that was not indexed by that list should be linear.
  irrelify-list-still-lin : ∀ { n m idx Aₗ } { Δ : Context n m }
    → (lin : cLinear Δ)
    → (lst : List (Fin m))
    → Unique (idx ∷ lst)
    → Aₗ ≡ Data.Vec.lookup (proj₂ (proj₁ (irrelify-List-lin Δ lst lin))) idx
    → proj₂ Aₗ ≡ Linear
  irrelify-list-still-lin {idx = zero} (lin/c lin) [] uniq refl = refl
  irrelify-list-still-lin {idx = suc idx} (lin/c lin) [] uniq refl = irrelify-list-still-lin lin [] ([] ∷ []) refl
  irrelify-list-still-lin {idx = zero} (lin/c lin) (zero ∷ lst) ((px ∷ x₁) ∷ uniq) refl = contradiction refl px
  irrelify-list-still-lin {idx = suc idx} (lin/c lin) (zero ∷ lst) ((px ∷ x₁) ∷ uniq) refl = {!  !}
  irrelify-list-still-lin (lin/c lin) (suc x ∷ lst) (x₁ ∷ uniq) refl = {!   !}

  ∈⇒idx : ∀ { p m Aₘ } ( Δ : Context p m )
    → Aₘ ∈ᵛ proj₂ Δ
    → Fin m
  ∈⇒idx Δ (here refl) = zero
  ∈⇒idx ⟨ fst , x ∷ xs ⟩ (there mem) = suc (∈⇒idx ⟨ fst , xs ⟩ mem)

  ∈≡idx : ∀ { p m Aₘ } ( Δ : Context p m )
    → ( idx : Fin m )
    → (mem : Aₘ ∈ᵛ proj₂ Δ)
    → idx ≡ ∈⇒idx Δ mem
    → Aₘ ≡ Data.Vec.lookup (proj₂ Δ) idx
  ∈≡idx { Aₘ = Aₘ } ⟨ fst , (x ∷ xs) ⟩ .(∈⇒idx { Aₘ = Aₘ } ⟨ fst , x ∷ xs ⟩ (here refl)) (here refl) refl = refl
  ∈≡idx ⟨ fst , (x ∷ xs) ⟩ .(∈⇒idx ⟨ fst , x ∷ xs ⟩ (there mem)) (there mem) refl = ∈≡idx ⟨ fst , xs ⟩ (∈⇒idx ⟨ fst , xs ⟩ mem) mem refl

  lookup⇒∈ : ∀ { p m Aₘ i } (Δ : Context p m )
    → Aₘ ≡ Data.Vec.lookup (proj₂ Δ) i 
    → Aₘ ∈ᵛ proj₂ Δ
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
    → Aₘ ∈ᵛ proj₂ (irrelify-AllBut Δ i)
  ∈-Δ⇒∈-IΔ {i = zero} {Δ = ⟨ fst , x ∷ snd ⟩} refl = here refl
  ∈-Δ⇒∈-IΔ {i = suc i} {Δ = ⟨ fst , x ∷ snd ⟩} refl = there (∈-Δ⇒∈-IΔ { Δ = ⟨ fst , snd ⟩ } refl)

  -- irrelify-allbut⇒update : ∀ { n m Aₘ i } { Δ Δ' : Context n m }
  --   → Aₘ ≡ (Data.Vec.lookup (proj₂ Δ) i)
  --   → Δ' ≡ irrelify-AllBut Δ i
  --   → Σ (Context n m) (λ Δ'' → update Δ' Aₘ (proj₁ Aₘ , Irrelevant) Δ'')
  -- irrelify-allbut⇒update {i = zero} {Δ = ⟨ fst , x ∷ snd ⟩} { Δ' = Δ' } refl refl 
  --   = ⟨ irrelify-Only Δ' zero , N ⟩
  -- irrelify-allbut⇒update {i = suc i} {Δ = ⟨ fst , x ∷ snd ⟩} {Δ' = Δ'} refl refl 
  --   = ⟨ ⟨ [] , ⟨ (proj₁ x) , Irrelevant ⟩ ∷ [] ⟩ ++ᶜ proj₁ IH , S (proj₂ IH) ⟩
  --     where
  --       IH = irrelify-allbut⇒update { i = i } { Δ = ⟨ fst , snd ⟩ } refl refl

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
  -- irrelify-allbut-upd-irrel-irr : ∀ { n m Aₘ i } { Δ Δ' Δ'' : Context n m }
  --   → (eq1 : Aₘ ≡ (Data.Vec.lookup (proj₂ Δ) i))
  --   → (eq2 : Δ' ≡ irrelify-AllBut Δ i)
  --   → (eq3 : Δ'' ≡ (proj₁ (irrelify-allbut⇒update eq1 eq2)))
  --   → cIrrelevant Δ''
  -- irrelify-allbut-upd-irrel-irr {i = zero} {⟨ fst , x ∷ snd ⟩} refl refl refl = irr/c (irrelify-irr ⟨ fst , snd ⟩)
  -- irrelify-allbut-upd-irrel-irr {i = suc i} {⟨ fst , x ∷ snd ⟩} refl refl refl = irr/c (irrelify-allbut-upd-irrel-irr { i = i } refl refl refl)

  -- Corollary to the above: the context attained is also weakeanable.
  -- irrelify-allbut-upd-irrel-weak : ∀ { n m Aₘ i } { Δ Δ' Δ'' : Context n m }
  --   → (eq1 : Aₘ ≡ (Data.Vec.lookup (proj₂ Δ) i))
  --   → (eq2 : Δ' ≡ irrelify-AllBut Δ i)
  --   → (eq3 : Δ'' ≡ (proj₁ (irrelify-allbut⇒update eq1 eq2)))
  --   → cWeakenable Δ''
  -- irrelify-allbut-upd-irrel-weak eq1 eq2 eq3 = cIrrelevant-to-cWeaken (irrelify-allbut-upd-irrel-irr eq1 eq2 eq3)

  -- Given a linear context that has been mostly irrelified,
  -- the irrelified form is its right identity in a merge operation.
  -- irrelify-lin-merge : ∀ { n m i } { Δ : Context n m }
  --   → cLinear Δ
  --   → merge (irrelify-AllBut Δ i) (irrelify-All Δ) (irrelify-AllBut Δ i)
  -- irrelify-lin-merge {i = zero} { Δ = ⟨ fst , x ∷ snd ⟩ } (lin/c lin) = mg/c (cIrrelevant-merge (irrelify-irr ⟨ fst , snd ⟩)) l∙i
  -- irrelify-lin-merge {i = suc i} (lin/c lin) = mg/c (irrelify-lin-merge lin) l∙i

  -- Given a linear context, its irrelified form is its left identity on the merge.
  irrelify-all-id-left : ∀ { n m } { Δ : Context n m }
    → LinOrIrr Δ
    → merge (irrelify-All Δ) Δ Δ
  irrelify-all-id-left lin/irr/z = mg/n
  irrelify-all-id-left (lin/irr/s-1 lin/irr) = mg/c (irrelify-all-id-left lin/irr) i∙l
  irrelify-all-id-left (lin/irr/s-2 lin/irr) = mg/c (irrelify-all-id-left lin/irr) i∙i

  -- Given a context that is linear, if we irrelified a list, a fully irrelified
  -- version of the same list would be the left identity of the merge operation.
  irrelify-all-list-merge : ∀ { n m } { Δ : Context n m }
    → (lst : List (Fin m))
    → (lin/irr : LinOrIrr Δ)
    → merge (irrelify-All Δ) (proj₁ (irrelify-List-lin/irr Δ lst lin/irr)) (proj₁ (irrelify-List-lin/irr Δ lst lin/irr))
  irrelify-all-list-merge {Δ = Δ} lst lin/irr with irrelify-List-lin/irr Δ lst lin/irr
  ... | ⟨ Δ' , ⟨ fst , snd ⟩ ⟩ = irrel-lin/irr-merge-id-left fst (irrelify-irr Δ) (comparable-trans Δ'-comp-Δ lem)
    where
      Δ'-comp-Δ : Comparable Δ' Δ
      Δ'-comp-Δ = comparable-comm snd

      lem : ∀ { n m } → { Δ : Context n m }
        → Comparable Δ (irrelify-All Δ)
      lem {Δ = ⟨ fst , [] ⟩} = comp/z
      lem {Δ = ⟨ fst , ⟨ fst₁ , Linear ⟩ ∷ snd ⟩} = comp/s lem
      lem {Δ = ⟨ fst , ⟨ fst₁ , Unrestricted ⟩ ∷ snd ⟩} = comp/s lem
      lem {Δ = ⟨ fst , ⟨ fst₁ , Irrelevant ⟩ ∷ snd ⟩} = comp/s lem

  irrelify-allbut-list-merge : ∀ { n m idx } { Δ : Context n m } { lst : List (Fin m) }
    → (lin : cLinear Δ)
    → (uniq-lst : Unique (idx ∷ lst))
    → merge (irrelify-AllBut Δ idx) (proj₁ (irrelify-List-lin Δ (idx ∷ lst) lin)) (proj₁ (irrelify-List-lin Δ lst lin))  
  irrelify-allbut-list-merge {idx = idx} {Δ = ⟨ fst , (⟨ A , Linear ⟩) ∷ snd ⟩} {lst} (lin/c lin) uniq-lst with irrelify-List-lin (⟨ fst , (⟨ A , Linear ⟩) ∷ snd ⟩) lst (lin/c lin)
  irrelify-allbut-list-merge {idx = zero} {⟨ fst , ⟨ A , Linear ⟩ ∷ snd ⟩} {lst} (lin/c lin) uniq-lst | ⟨ ⟨ .fst , .(⟨ A , Linear ⟩ ∷ _) ⟩ , ⟨ lin/irr/s-1 fst₁ , comp/s snd₁ ⟩ ⟩ = {!   !}
  irrelify-allbut-list-merge {idx = suc idx} {⟨ fst , ⟨ A , Linear ⟩ ∷ snd ⟩} {lst} (lin/c lin) uniq-lst | ⟨ ⟨ .fst , .(⟨ A , Linear ⟩ ∷ _) ⟩ , ⟨ lin/irr/s-1 fst₁ , comp/s snd₁ ⟩ ⟩ = {!   !}
  irrelify-allbut-list-merge {idx = zero} {⟨ fst , ⟨ A , Linear ⟩ ∷ snd ⟩} {lst} (lin/c lin) (idx-uniq ∷ uniq-lst) | ⟨ ⟨ .fst , ⟨ A , Irrelevant ⟩ ∷ Δ' ⟩ , ⟨ lin/irr/s-2 fst₁ , comp/s snd₁ ⟩ ⟩ = ?
  irrelify-allbut-list-merge {idx = suc idx} {⟨ fst , ⟨ A , Linear ⟩ ∷ snd ⟩} {lst} (lin/c lin) uniq-lst | ⟨ ⟨ .fst , .(⟨ A , Irrelevant ⟩ ∷ _) ⟩ , ⟨ lin/irr/s-2 fst₁ , comp/s snd₁ ⟩ ⟩ = {!   !}
