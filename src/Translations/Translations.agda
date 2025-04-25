open import Data.Vec
open import Data.List
open import Data.Nat using (_+_; z≤n; ℕ)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵛ_)
open import Data.Vec.Relation.Unary.Any
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
open import Data.Bool

module Translations.Translations where
  {- Repackage other pieces of the translation -}
  open import Translations.Core.Term public
  open import Translations.Core.PropAtom public
  open import Translations.Core.Condition public
  open import Translations.Core.ConditionConfiguration public
  open import Translations.Core.State public
  open import Translations.Core.Goal public
  open import Translations.Core.Operator public
  
  open import STRIPS.Problem
  open import ADJ.Core

  open import Utils.AllOfMode
  open import Utils.BigTensor
  
  {-
    Here, we define the problem translation function in pieces.
  -}
  -- Some helper functions

  -- Expected length of the term context, which will consist of
  -- all translated terms of P plus "true" and "false"
  lenTermCtxt : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾 → ℕ
  lenTermCtxt (wf/prob 𝕋 _ _ _ _ _ _ _) = Data.List.length 𝕋

  -- Expected length of the unrestricted context, which will
  -- consist of all translated operators of P
  lenUnrCtxt : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾  → ℕ
  lenUnrCtxt (wf/prob _ _ _ 𝕆 _ _ _ _) = Data.List.length 𝕆

  -- -- Expected length of the linear context, which will
  -- -- consist of all translated conditions of P
  lenLinCtxt : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾  → ℕ
  lenLinCtxt (wf/prob _ ℂ _ _ _ _ _ _) = Data.List.length ℂ

  -- -- The expected size of the context of the sequent
  -- -- obtained from translating a problem is the size of
  -- -- the term context (plus 0) and the combined length of
  -- -- the unrestricted and linear contexts. We need the plus 0
  -- -- because we are going to get the translated context through
  -- -- concatenation.
  CtxtP : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾  → Set
  CtxtP (wf/prob 𝕋 ℂ _ 𝕆 _ _ _ _) = Context (2 + Data.List.length 𝕋 + 0) (Data.List.length 𝕆 + Data.List.length ℂ)

  -- {- 
  --   Translation of operators into an unrestricted context.
  --   We prove that this part of the context is indeed unrestricted below.
  -- -}
  contextify-operators : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾  → Context (2 + Data.List.length 𝕋) (Data.List.length 𝕆)
  contextify-operators P = ⟨ const "true" ∷ const "false" ∷ translTsOfP P , translO P ⟩
  -- {-
  --   Translation of state into a linear context.
  --   We prove that this part of the context is indeed linear below.
  -- -}
  contextify-state : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾  → Context 0 (Data.List.length 𝕀) 
  contextify-state P = ⟨ [] , translS P ⟩

  -- {-
  --   Concatenates the operator and state contexts.
  -- -}
  contextOfProblem : ∀ (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)  
    → Context ((2 + Data.List.length 𝕋) + 0) ((Data.List.length 𝕆) + (Data.List.length 𝕀))
  contextOfProblem P = contextify-operators P ++ᶜ contextify-state P

  -- {-
  --   The main translation function. Given a PlanProblem, output the translated context
  --   and translated goal as a proposition. We omit the mode of the goal context here. We
  --   will assume that it's linear in our proofs.
  -- -}
  translProb : ∀ (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) 
    → (Context ((2 + Data.List.length 𝕋) + 0) ((Data.List.length 𝕆) + (Data.List.length 𝕀))) × (Prop × Mode) 
  translProb ℙ = ⟨ (contextOfProblem ℙ) , translG ℙ ⟩

  -- {------
  -- - Properties of translations
  -- ------}

  -- {- Properties of problem translation -}
  ∈-state⇒∈-state-context : ∀ { s } → (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾)
    → s ∈ˡ 𝕀
    → ⟨ translConfig-Condition s , Linear ⟩ ∈ᵛ (proj₂ (contextify-state ℙ))
  ∈-state⇒∈-state-context {𝕀 = 𝕀} {s = ⟨ fst , false ⟩} (wf/prob _ _ .(⟨ fst , false ⟩ ∷ _) _ _ wf/conds wf/state wf/goal) (here refl) = here refl
  ∈-state⇒∈-state-context {𝕀 = 𝕀} {s = ⟨ fst , true ⟩} (wf/prob _ _ .(⟨ fst , true ⟩ ∷ _) _ _ wf/conds wf/state wf/goal) (here refl) = here refl
  ∈-state⇒∈-state-context (wf/prob _ _ .(⟨ fst , false ⟩ ∷ xs) 𝕆 _ wf/conds (wf/state/s wf/state x) wf/goal) (there {⟨ fst , false ⟩} {xs = xs} mem) 
    = there (∈-state⇒∈-state-context (wf/prob _ _ xs 𝕆 _ wf/conds wf/state wf/goal) mem)
  ∈-state⇒∈-state-context (wf/prob _ _ .(⟨ fst , true ⟩ ∷ xs) 𝕆 _ wf/conds (wf/state/s wf/state x) wf/goal) (there {⟨ fst , true ⟩} {xs = xs} mem) 
    = there (∈-state⇒∈-state-context (wf/prob _ _ xs 𝕆 _ wf/conds wf/state wf/goal) mem)

  ∈-state-context⇒∈-context : ∀ { s } → (ℙ : PlanProblem 𝕋 ℂ 𝕀 𝕆 𝔾) 
    → s ∈ᵛ (proj₂ (contextify-state ℙ))
    → s ∈ᵛ (proj₂ (contextOfProblem ℙ))
  ∈-state-context⇒∈-context {𝕆 = []} (wf/prob _ _ _ .[] _ wf/conds wf/state wf/goal) mem = mem
  ∈-state-context⇒∈-context {𝕆 = x ∷ 𝕆} (wf/prob _ _ 𝕀 .(x ∷ 𝕆) _ wf/conds wf/state wf/goal) mem 
    = there (∈-state-context⇒∈-context (wf/prob _ _ 𝕀 𝕆 _ wf/conds wf/state wf/goal) mem)

  