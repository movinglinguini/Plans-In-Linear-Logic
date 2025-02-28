open import Data.String hiding (_≟_)
open import Data.Nat
open import Data.Fin hiding (_≟_)
open import Data.Vec
open import Relation.Nullary.Decidable

module ADJ.Core2 where
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Terms String

  data Prop+ : Set where
    𝟙 : Prop+
    `_ : Proposition → Prop+
    _⊗_ : Prop+ → Prop+ → Prop+

  data Rule : ℕ → Set where
    r : ∀ { n } → Prop+ → Prop+ → Rule n


  ex1 : Rule 4
  ex1 = r
          (` v[ (record { name = "p" ; terms = var (suc (suc (zero))) ∷ [] }) , var zero ]) 
          ((` v[ (record { name = "q" ; terms = var (suc (suc (suc (zero)))) ∷ [] }) , var (suc zero) ]))
  
  subst-term : ℕ → Term → Term → Term
  subst-term idx t₁ (const x) = const x
  subst-term idx t₁ (var x) with idx ≟ x
  ... | yes _ = t₁
  ... | no _ = var x

  subst-terms : ∀ { n } → ℕ → Term → Vec Term n → Vec Term n 
  subst-terms _ _ [] = []
  subst-terms idx t (x ∷ xs) = subst-term idx t x ∷ subst-terms idx t xs

  subst-condition : ℕ → Term → TCondition → TCondition
  subst-condition idx t record { arity = arity ; name = name ; terms = terms } = record { name = name ; terms = subst-terms idx t terms }

  subst-proposition : ℕ → Term → Proposition → Proposition
  subst-proposition idx t v[ A , t' ] = v[ (subst-condition idx t A) , subst-term idx t t' ]

  subst-prop+ : ℕ → Term → Prop+ → Prop+
  subst-prop+ _ t 𝟙 = 𝟙
  subst-prop+ idx t (` x) = ` (subst-proposition idx t x)
  subst-prop+ idx t (A ⊗ A₁) = (subst-prop+ idx t A) ⊗ (subst-prop+ idx t A₁)

  rule-app : ∀ { n } → ℕ → Rule n → Vec (Term) n → Rule 0
  rule-app i (r L R) [] = r L R    
  rule-app i (r L R) (t ∷ T) = 
      let L' = subst-prop+ i t L 
          in let R' = subst-prop+ i t R 
            in rule-app (suc i) (r L' R') T

  T : Vec Term 4
  T = const "true" ∷ const "false" ∷ const "a" ∷ const "b" ∷ []

  ex1-subst = rule-app 0 ex1 T

  -- Why no normalize????????? >:(
  test = subst-condition 0 (const "true")
    (record
     { name = "p" ; terms = var 2 ∷ [] })

  open import PrettyPrinter.PrettyPrinter 3000

  test-string = render (prettyTCondition test)

  test2 = subst-terms 0 (const "true") (var 2 ∷ var 0 ∷ [])