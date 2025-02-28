{-
  Instantiates ADJ Logic with modes, a preorder on modes, a decidable preorder on modes, and a base type
  to construct propositions from.
-}
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Nat
open import Data.Vec
open import Data.Bool hiding (_≟_)

module ADJ.Core where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props Proposition public
  open import Logic.Core.Terms TermAtom public
  open import Logic.Core.Modes public
  open import Logic.Core.Contexts Proposition TermAtom public
  open import Logic.Utils.ModeOf Proposition public

  private
    {-
      Here, we define the substitution function.
    -}
    subst-TCondition-Terms : ∀ { n } → Vec Term n → Term → Vec Term n
    subst-TCondition-Terms [] t = []
    subst-TCondition-Terms (const x ∷ T) t = const x ∷ (subst-TCondition-Terms T t)
    subst-TCondition-Terms (var x ∷ T) t with x
    ... | zero = t ∷ subst-TCondition-Terms T t
    ... | suc x = var x ∷ subst-TCondition-Terms T t

    subst-TCondition : TCondition → Term → TCondition
    subst-TCondition record { name = name ; terms = args } t = record { name = name ; terms = (subst-TCondition-Terms args t) }

    subst : Prop → Term → Prop
    subst (` v[ p , b ]) t with b
    ... | const x = ` v[ (subst-TCondition p t) , (const x) ]
    ... | var x with x
    ...   | zero = ` v[ (subst-TCondition p t), t ]
    ...   | suc x = ` v[ (subst-TCondition p t) , var x ]
    subst (p₁ ⊸ p₂) t = (subst p₁ t) ⊸ (subst p₂ t)
    subst (p₁ ⊗ p₂) t = ((subst p₁ t)) ⊗ subst p₂ t
    subst 𝟙 t = 𝟙
    subst ⊤ t = ⊤
    subst (p₁ ⊕ p₂) t = subst p₁ t ⊕ subst p₂ t
    subst (p₁ & p₂) t = (subst p₁ t) & subst p₂ t
    subst (↑[ x ][ x₁ ] p) t = ↑[ x ][ x₁ ] (subst p t)
    subst (↓[ x ][ x₁ ] p) t = ↓[ x ][ x₁ ] (subst p t)
    subst ∀[ ∀[ p ] ] t = ∀[ subst ∀[ p ] t ]
    subst ∀[ p ] t = subst p t

    -- Test out substitution
    cond1 : TCondition
    cond1 = record { name = "cond-1" ; terms = var 0 ∷ const "t1" ∷ [] }

    cond2 : TCondition
    cond2 = record { name = "cond-2" ; terms = var 1 ∷ const "t2" ∷ [] }

    cond1trans : TCondition
    cond1trans = record { name = "cond-1" ; terms = const "s1" ∷ const "t1" ∷ [] }

    cond2trans1 : TCondition
    cond2trans1 = record { name = "cond-2" ; terms = var 0 ∷ const "t2" ∷ [] }

    prop1 : Prop
    prop1 = ∀[ ∀[ (` v[ cond1 , const "b1" ]) ⊸ (` v[ cond2 , var 0 ])  ]  ]

    _ : subst prop1 (const "s1") ≡ ∀[ (` v[ cond1trans , const "b1" ]) ⊸ (` v[ cond2trans1 , const "s1" ] ) ]
    _ = refl 

  open import Logic.Adjoint Proposition TermAtom subst public
