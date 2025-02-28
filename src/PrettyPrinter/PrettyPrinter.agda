open import Data.Nat
open import Data.Nat.Show
open import Data.Vec using (toList; Vec)
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module PrettyPrinter.PrettyPrinter (width : ℕ) where
  open import Text.Pretty width public

  open import Translations.Core.Condition
  open import Translations.Core.State
  open import ADJ.Core
  
  {-
    Pretty print props
  -}
  prettyTerm : Term → Doc
  prettyTerm (const x) = text x
  prettyTerm (var x) = char '#' <> (text (show x))
  
  prettyTCondition : TCondition → Doc
  prettyTCondition record { name = name ; terms = args } 
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

  prettyPropxMode : (Prop × Mode) → Doc
  prettyPropxMode ⟨ A , m ⟩ = prettyProp A

  prettyContext : ∀ { x y } → Context x y → Doc
  prettyContext ⟨ fst , snd ⟩ = prettyContext-helper fst prettyTerm <> char ';' <+> prettyContext-helper snd prettyPropxMode
    where
      prettyContext-helper : ∀ { A n } → Vec A n → (A → Doc) → Doc 
      prettyContext-helper Vec.[] f = empty
      prettyContext-helper (x Vec.∷ V) f = f x <> char ',' <+> prettyContext-helper V f

  prettyProblem : ∀ { x y } → (Context x y) × Prop → Doc
  prettyProblem ⟨ fst , snd ⟩ = prettyContext fst <+> char '⊢' <+> prettyProp snd <+> char '⊗' <+> char '⊤'