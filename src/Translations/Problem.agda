open import Plans.Domain
open import Data.List hiding (List)

import ADJ.Core
import Utils.BigTensor

module Translations.Problem 
  (domain : Domain) 
  (Term : Set)
  where

  open Domain domain

  open ADJ.Core PredMap Term
  open Utils.BigTensor PredMap Term using (⨂_)

  goalJgmt = ( actions : List (Prop Unrestricted) ) ( init : List (Prop Linear)  ) ( goal : Prop Linear ) → ((toHProps actions) ++ (toHProps init)) ⊢ goal ⊗ ⊤
