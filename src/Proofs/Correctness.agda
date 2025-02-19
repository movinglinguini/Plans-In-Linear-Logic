-- open import Data.List using (List; _∷_; []; map)
-- open import Data.Vec
-- open import Data.Product renaming (_,_ to ⟨_,_⟩)
-- open import Plans.Domain
-- open import Relation.Binary.PropositionalEquality
-- open import Data.List.Membership.Propositional
-- open import Data.List.Relation.Binary.Sublist.Propositional
-- open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List hiding (merge)
open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Proofs.Correctness where
  open import STRIPS.Problem renaming (Term to STRIPSTerm)
  open import Translations.Translations
  open import ADJ.Core renaming (Term to AdjointTerm)

  {- Helper functions -}
  makeAllIrrel : ∀ { n m } → Context n m → Context n m
  makeAllIrrel ⟨ fst , snd ⟩ = ⟨ fst , irrelify snd ⟩
    where
      irrelify : ∀ { n } → Vec (Prop × Mode) n → Vec (Prop × Mode) n
      irrelify [] = []
      irrelify (x ∷ xs) = ⟨ proj₁ x , Irrelevant ⟩ ∷ irrelify xs 

  data Irrelified : ∀ { n m } → Context n m → Context n m → Set where
    irrelify/z : ∀ { n } → { T : Vec AdjointTerm n } → Irrelified ⟨ T , [] ⟩ ⟨ T , [] ⟩
    irrelify/s : ∀ { n m A k } → { T : Vec AdjointTerm n } { Δ IΔ : Vec (Prop × Mode) m }
      → Irrelified ⟨ T , Δ ⟩ ⟨ T , IΔ ⟩
      -----------------------
      → Irrelified ⟨ T , ⟨ A , k ⟩ ∷ Δ ⟩ ⟨ T , ⟨ A , Irrelevant ⟩ ∷ IΔ ⟩
  
  private 
    variable
      𝕀 ℙ : List Condition
      𝕀ᵗ : Vec (Prop × Mode) (Data.List.length ℙ)
      𝔾 : Goal
      𝔾ᵗ : Prop × Mode
      𝕋 : List STRIPSTerm
      𝕋ᵗ : Vec AdjointTerm (Data.List.length 𝕋)

  sat𝕀⟨𝔾⟩⇒proof : ∀ { n m } → { Δ : Context n m } 
    → TranslTs 𝕋 𝕋ᵗ
    → TranslS 𝕀 ℙ 𝕀ᵗ
    → TranslG 𝔾 𝔾ᵗ
    → sat 𝕀 ⟨ Goal.pos 𝔾 , Goal.neg 𝔾 ⟩
    → Δ ⊢ⁱ 𝔾ᵗ

  sat𝕀⟨𝔾⟩⇒proof {n = n} {m = m} {Δ = ⟨ fst , [] ⟩} tT tS translG/z sat = {!   !}
    where
      IΔ : Context n m
      IΔ = makeAllIrrel ⟨ fst , [] ⟩

      isIrrel : Irrelified ⟨ fst , [] ⟩ IΔ
      isIrrel = irrelify/z

      contractableIΔ : cContractable IΔ
      contractableIΔ = cont/n

      M12 : merge IΔ IΔ IΔ
      M12 = mg/n
      M23 : merge IΔ Δ Δ
      M23 = {!   !}
      M : merge IΔ Δ Δ

  sat𝕀⟨𝔾⟩⇒proof {n = n} {m = m} {Δ = ⟨ fst , x ∷ snd ⟩} tT tS translG/z sat = {!   !} -- ⊗R M12 M23 M {!   !} (𝟙R {!   !}) ⊤R

  sat𝕀⟨𝔾⟩⇒proof tT tS translG/s sat = {!   !}
  {-
    This is the main theorem we want to prove. If we have a planning solution, we have a proof of
    the problem's translation.
  -}
  correctness : ∀ { P : Plan } { 𝕀 ℙ : List Condition } { 𝕋 : List STRIPSTerm } { 𝕆 : List Operator } { 𝔾 : Goal }
    { 𝕋ᵗ : Vec AdjointTerm (Data.List.length 𝕋)} { 𝕀ᵗ : Vec (Prop × Mode) (Data.List.length ℙ) } { 𝔾ᵗ : Prop × Mode } { 𝕆ᵗ : Vec (Prop × Mode) (Data.List.length 𝕆) }
    { Γ : Context (Data.Vec.length 𝕋ᵗ) (Data.Vec.length 𝕆ᵗ) } { Δ : Context 0 (Data.Vec.length 𝕀ᵗ) }   
    → TranslTs 𝕋 𝕋ᵗ
    → TranslS 𝕀 ℙ 𝕀ᵗ
    → TranslOs 𝕆 𝕆ᵗ
    → TranslG 𝔾 𝔾ᵗ
    → Contextify 𝕋ᵗ 𝕆ᵗ Γ
    → Contextify [] 𝕀ᵗ Δ
    → Solves 𝕀 P 𝔾
    → (Γ ++ᶜ Δ) ⊢ⁱ 𝔾ᵗ
   
  correctness tT tS tO tG cΓ cΔ (solves/z x) = sat𝕀⟨𝔾⟩⇒proof tT tS tG x 
  correctness _ _ _ _ _ _ (solves/s plan-solves x) = {!   !}   