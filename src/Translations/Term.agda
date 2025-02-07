module Translations.Term (TermAtom : Set) where
  open import STRIPS.Problem TermAtom renaming (Term to STRIPSTerm)
  open import Logic.Core.Terms TermAtom renaming (Term to ADJTerm)

  translT : STRIPSTerm → ADJTerm 
  translT (term x) = term x
  translT (var x) = var x
