open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Plans.Domain

{--
For pretty printing
-}
open import Text.Pretty 80
open import Data.Nat.Show

module Translations.State (domain : Domain) where
  open Domain domain
  open import Syntax.Core domain

  translPredmap : PredMap → Proposition
  translPredmap ⟨ polarity , pred ⟩ with polarity
  ... | + = v[ pred , true ]
  ... | - = v[ pred , false ]
  
  open import ADJ.Core Proposition Term using (Prop; Linear)
  
  translS : State → List (Prop Linear)
  translS S = Data.List.map (Prop.`_) (Data.List.map translPredmap S)

  {-

  -}
  -- WFSTranslation : State → List (Prop Linear) → Set
  -- WFSTranslation S St = 
  --   ∀ { s st S' St' } → S ≡ (s ∷ S') → St ≡ (st ∷ St') → st ≡ Prop.` (translPredmap s) 
  transl-nonempty : ∀ { s S' } (S : State) (St : List (Prop Linear)) → S ≡ (s ∷ S') → St ≡ translS S → St ≡ (Prop.` translPredmap s ∷ translS S')
  transl-nonempty (x ∷ S) (.(Prop.` translPredmap x) ∷ .(Data.List.map Prop.`_ (Data.List.map translPredmap S))) refl refl = refl

  head-translation-lemma : ∀ { s st S' St' } (S : State) (St : List (Prop Linear)) → S ≡ (s ∷ S') → St ≡ (st ∷ St') → St ≡ translS S → st ≡ Prop.` translPredmap s
  head-translation-lemma {s} {.(Prop.` translPredmap s)} {S'} {.(Data.List.map Prop.`_ (Data.List.map translPredmap S'))} (s ∷ S') (.(Prop.` translPredmap s) ∷ .(Data.List.map Prop.`_ (Data.List.map translPredmap S'))) refl refl refl = refl

  tail-translation-lemma : ∀ { s st S' St' } (S : State) (St : List (Prop Linear)) → S ≡ (s ∷ S') → St ≡ (st ∷ St') → St ≡ translS S → St' ≡ translS S'
  tail-translation-lemma {s} {.(Prop.` translPredmap s)} {S'} {.(Data.List.map Prop.`_ (Data.List.map translPredmap S'))} .(s ∷ S') .(Prop.` translPredmap s ∷ Data.List.map Prop.`_ (Data.List.map translPredmap S')) refl refl refl = refl

  pos-case : ∀ { p p[t] } → p ≡ ⟨ + , p[t] ⟩ → translPredmap p ≡ v[ p[t] , true ]
  pos-case refl = refl

  invert-pos-case : ∀ { p p[t] } → translPredmap p ≡ v[ p[t] , true ]  → p ≡ ⟨ + , p[t] ⟩
  invert-pos-case {⟨ + , snd ⟩} {.snd} refl = refl

  neg-case : ∀ { p p[t] } → p ≡ ⟨ - , p[t] ⟩ → translPredmap p ≡ v[ p[t] , false ]
  neg-case refl = refl

  invert-neg-case : ∀ { p p[t] } → translPredmap p ≡ v[ p[t] , false ]  → p ≡ ⟨ - , p[t] ⟩
  invert-neg-case {⟨ - , snd ⟩} {.snd} refl = refl

  -- WFSTranslation : ∀ { s S' st St' } (S : State) (St : List (Prop Linear)) → S ≡ (s ∷ S') → St ≡ translS S → St' ≡ translS S' → (St ≡ (st ∷ St') × st ≡ Prop.` translPredmap s)
  -- WFSTranslation S St S-nonempty St-is-tranlSS subtranslation = {!   !}
  --   where
      
  -- wf-state-nonempty = ∀ { S St } → WFSTranslation S St → 
    