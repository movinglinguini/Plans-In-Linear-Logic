open import Plans.Domain
open import Data.List

import ADJ.Core
import Utils.BigTensor

module Translations.Goal (domain : Domain) (Term : Set) where

  open Domain domain

  open ADJ.Core PredMap Term
  open Utils.BigTensor PredMap Term using (⨂_)

  translG : GoalState → Prop Linear
  translG G = ⨂ (map (λ g → ` g) G)
