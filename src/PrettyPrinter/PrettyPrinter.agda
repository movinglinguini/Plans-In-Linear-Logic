open import Data.Nat
open import Data.Fin.Show renaming (show to showF)
open import Data.Nat.Show renaming (show to showN)
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
  prettyTerm : ∀ { s } → Term s → Doc
  prettyTerm (const x) = text x
  prettyTerm (var x) = char '#' <> (text (showF x))
  
  prettyTCondition : ∀ { s } → TCondition s → Doc
  prettyTCondition record { label = label ; terms = args } 
    = text label <> parens (termDocs)
    where
      termDocs : Doc
      termDocs = foldr (λ t acc → (prettyTerm t) <> char ',' <+> acc) empty (toList args)


  prettyPropAtom : PropAtom → Doc
  prettyPropAtom v[ x , x₁ ] = char 'v' <> parens (prettyTCondition x <> char ',' <+> prettyTerm x₁)

  prettyProp : Prop → Doc
  prettyProp (` A) = prettyPropAtom A
  prettyProp (A ⊸ B) = prettyProp A <+> char '⊸' <+> prettyProp B
  prettyProp (A ⊗ B) = prettyProp A <+> char '⊗' <+> prettyProp B
  prettyProp 𝟙 = char '𝟙'
  prettyProp ⊤ = char '⊤'
  prettyProp ∀[ n ][ A ] = char '∀' <> char '{' <> (text (showN n)) <> char '}' <> parens (prettyProp A)

  prettyPropxMode : (Prop × Mode) → Doc
  prettyPropxMode ⟨ A , m ⟩ = prettyProp A

  prettyContext : ∀ { x y } → Context x y → Doc
  prettyContext ⟨ fst , snd ⟩ = prettyContext-helper fst prettyTerm <> char ';' <+> prettyContext-helper snd prettyPropxMode
    where
      prettyContext-helper : ∀ { A n } → Vec A n → (A → Doc) → Doc 
      prettyContext-helper Vec.[] f = empty
      prettyContext-helper (x Vec.∷ V) f = f x <> char ',' <+> prettyContext-helper V f

  prettyProblem : ∀ { x y } → (Context x y) × (Prop × Mode) → Doc
  prettyProblem ⟨ fst , snd ⟩ = prettyContext fst <+> char '⊢' <+> prettyPropxMode snd