open import Data.Nat
open import Data.Nat.Show
open import Plans.Domain

module ADJ.PrettyPrinter (domain : Domain) (width : ℕ) where

  open import Text.Pretty width
  open Domain domain  
  open import Syntax.Core domain renaming (Term to BaseTerm)
  open import ADJ.Core domain renaming (Context to Ctxt)

  module PrettyPrint (prettyPred : Predicate → Doc) where
    prettyTerm : BaseTerm → Doc 
    prettyTerm true = text "true" 
    prettyTerm false = text "false"
    prettyTerm (var x) = char '#' <> text (show x)

    prettyProposition : Proposition → Doc
    prettyProposition v[ p , t ] = char 'v' <> (parens ((prettyPred p) <> char ',' <+> (prettyTerm t)))

    prettyProp : Prop → Doc
    prettyProp (` A) = prettyProposition A
    prettyProp (p ⊸ p₁) = prettyProp p <+> (char '⊸') <+> prettyProp p₁
    prettyProp (p ⊗ p₁) = prettyProp p <+> (char '⊗') <+> prettyProp p₁
    prettyProp 𝟙 = char '𝟙' 
    prettyProp ⊤ = char '⊤'
    prettyProp (p ⊕ p₁) = prettyProp p <+> (char '⊕') <+> prettyProp p₁
    prettyProp (p & p₁) = prettyProp p <+> (char '&') <+> prettyProp p₁
    prettyProp (↑[ x ][ y ] p) = text "↑" <> (parens (prettyProp p))
    prettyProp (↓[ x ][ y ] p) = text "↓" <> (parens (prettyProp p))
    prettyProp (∀[ p ]) = char ('∀') <> (parens (prettyProp p))

