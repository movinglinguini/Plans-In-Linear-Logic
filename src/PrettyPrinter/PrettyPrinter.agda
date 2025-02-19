open import Data.Nat
open import Data.Nat.Show
open import Data.Vec using (toList)
open import Data.List

module PrettyPrinter.PrettyPrinter (width : ℕ) where
  open import Text.Pretty width public

  open import Translations.Translations
  open import ADJ.Core
  
  {-
    Pretty print props
  -}
  prettyTerm : Term → Doc
  prettyTerm (term x) = text x
  prettyTerm (var x) = char '#' <> (text (show x))
  
  prettyTCondition : TCondition → Doc
  prettyTCondition record { name = name ; args = args } 
    = text name <> parens (termDocs)
    where
      termDocs : Doc
      termDocs = foldr (λ t acc → (prettyTerm t) <> char ',' <+> acc) empty (toList args)


  prettyProposition : Proposition → Doc
  prettyProposition v[ x , x₁ ] = char 'v' <> parens (prettyTCondition x <> char ',' <+> prettyTerm x₁)

  prettyProp : Prop → Doc
  prettyProp (` A) = prettyProposition A
  prettyProp (A ⊸ B) = prettyProp A <+> char '⊸' <+> prettyProp B
  prettyProp (A ⊗ B) = prettyProp A <+> char '⊗' <+> prettyProp B
  prettyProp 𝟙 = char '𝟙'
  prettyProp ⊤ = char '⊤'
  prettyProp (A ⊕ B) = prettyProp A <+> char '⊕' <+> prettyProp B
  prettyProp (A & B) = prettyProp A <+> char '&' <+> prettyProp B
  prettyProp (↑[ x ][ x₁ ] A) = char '↑' <> (prettyProp A)
  prettyProp (↓[ x ][ x₁ ] A) = char '↓' <> (prettyProp A)
  prettyProp ∀[ A ] = char '∀' <> parens (prettyProp A)