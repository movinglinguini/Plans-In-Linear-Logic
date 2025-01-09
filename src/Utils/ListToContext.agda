module ListToContext (U : Set) (T : Set) where
  open import Translations
  open import ADJ.Core 

  listToContext : ∀ { m } → List (Prop m) → Context