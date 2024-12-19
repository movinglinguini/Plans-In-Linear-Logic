open import Text.Pretty 80
open import Data.Nat.Show
open import Plans.Domain

module ADJ.PrettyPrinter (domain : Domain) where

  open Domain domain
  open import Translations.State domain
  open import ADJ.Core Proposition

  module PrettyPrint (prettyPred : Predicate → Doc) where
    prettyTerm : Term → Doc 
    prettyTerm true = text "true" 
    prettyTerm false = text "false"
    prettyTerm (var x) = char '#' <> text (show x)

    prettyProposition : Proposition → Doc
    prettyProposition v[ p , t ] = char 'v' <> (parens ((prettyPred p) <> char ',' <+> (prettyTerm t)))

    prettyProp : ∀ { m : Mode } → Prop m → Doc
    prettyProp (` A) = prettyProposition A
    prettyProp (p ⊸ p₁) = prettyProp p <+> (char '⊸') <+> prettyProp p₁
    prettyProp (p ⊗ p₁) = prettyProp p <+> (char '⊗') <+> prettyProp p₁
    prettyProp 𝟙 = char '𝟙' 
    prettyProp ⊤ = char '⊤'
    prettyProp (p ⊕ p₁) = prettyProp p <+> (char '⊕') <+> prettyProp p₁
    prettyProp (p & p₁) = prettyProp p <+> (char '&') <+> prettyProp p₁
    prettyProp (Up[ x ] p) = text "↑." <> (parens (prettyProp p))
    prettyProp (Down[ x ] p) = text "↓." <> (parens (prettyProp p))
    prettyProp (all p) = text ("∀.") <> prettyProp p

    prettyHprop : HProp → Doc
    prettyHprop (HProp.` x) = prettyProp x