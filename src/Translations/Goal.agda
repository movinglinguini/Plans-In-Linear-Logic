open import Plans.Domain
open import Data.List

import ADJ.Core
import Utils.BigTensor

module Translations.Goal (domain : Domain) where

  open Domain domain

  open import Translations.State domain
  open ADJ.Core Proposition
  open Utils.BigTensor Proposition using (⨂_)

  translG : GoalState → Prop Linear
  translG G = ⨂ (translS G)
