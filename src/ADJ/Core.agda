{-
  Instantiates ADJ Logic with modes, a preorder on modes, a decidable preorder on modes, and a base type
  to construct propositions from.
-}
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Bool hiding (_≟_)

module ADJ.Core where
  open import STRIPS.Problem hiding (Term)
  open import Translations.Core.Condition
  open import Translations.Core.State
  open import Logic.Core.Props PropAtom public
  open import Logic.Core.Terms TermAtom public
  open import Logic.Core.Modes public
  open import Logic.Core.Contexts PropAtom TermAtom public
  open import Logic.Utils.ModeOf PropAtom public

  private
    subst-Term : ∀ { s } → Term s → Term 0 → Term s
    subst-Term (const x) _ = const x
    subst-Term (var zero) (const x) = const x
    subst-Term (var (suc m)) _ = var (inject₁ m)

    subst-Terms : ∀ { s n } → Vec (Term s) n → Term 0 → Vec (Term s) n 
    subst-Terms [] t = []
    subst-Terms (x ∷ ts) t = (subst-Term x t) ∷ (subst-Terms ts t)

    subst-TCondition : ∀ { s } → TCondition s → Term 0 → TCondition s
    subst-TCondition TC t = record { label = (TCondition.label TC) ; terms = subst-Terms (TCondition.terms TC) t }

    -- Helper function for substitution that's needed by the Adjoint Logic module.
    -- Scans over the PropAtom, and replaces all var 0's with t. As it scans,
    -- all non-var 0's are decremented.
    subst-PropAtom : PropAtom → Term 0 → PropAtom
    subst-PropAtom v[ TC , tv ] t = v[ subst-TCondition TC t , subst-Term tv t ]

  -- Instantiate the Adjoint Logic with atoms for Props and Terms, and a
  -- function for substitution in PropAtoms.
  open import Logic.Adjoint PropAtom TermAtom subst-PropAtom public
  
  private
    -- Let's test out substitution 
    -- Setting up the conditions to be used as atoms for our props
    -- Left side of the source Prop
    sTCondL : TCondition 2
    sTCondL = record { label = "p1" 
                ; terms = var zero ∷ var (suc zero) ∷ [] }
    -- Right side of the target Prop
    sTCondR : TCondition 2
    sTCondR = record { label = "p2" 
                ; terms = var (suc zero) ∷ const "t" ∷ var zero ∷ [] }

    sProp : Prop
    sProp = ∀[ 1 ][ ` v[ sTCondL , var zero ] ⊸ ` v[ sTCondR , const "false" ] ]

    terms : Vec (Term 0) 2
    terms = const "t0" ∷ const "t1" ∷ []

    tProp = subst sProp terms
    {-
      Expecting tProp to look like
      v[ p1( t0, t1 ) , t0 ] ⊸ v[ p2(t1, t, t0), false ]
    -}