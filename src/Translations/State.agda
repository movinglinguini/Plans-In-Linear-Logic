open import Data.Nat
open import Data.List
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

  private
    translPredmap : PredMap → Proposition
    translPredmap ⟨ polarity , pred ⟩ with polarity
    ... | + = v[ pred , true ]
    ... | - = v[ pred , false ]
  
  open import ADJ.Core Proposition Term using (Prop; Linear)
  
  translS : State → List (Prop Linear)
  translS S = Data.List.map (Prop.`_) (Data.List.map translPredmap S)
