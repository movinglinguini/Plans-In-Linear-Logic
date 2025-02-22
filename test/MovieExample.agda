open import Data.List
open import Data.Vec
open import Data.Irrelevant
open import Data.Maybe
open import Data.Fin
open import Data.Product
open import Data.String

open import STRIPS.Problem

module MovieExample where
  conditions : List Condition
  conditions = (record { name = "movie-rewound" ; args = [] }) ∷
      (record { name = "counter-at-two-hours" ; args = [] }) ∷ 
      (record { name = "counter-at-other-than-two-hours" ; args = [] }) ∷ 
      (record { name = "counter-at-zero" ; args = [] }) ∷ 
      (record { name = "have-chips" ; args = [] }) ∷ 
      (record { name = "have-dip" ; args = [] }) ∷ 
      (record { name = "have-pop" ; args = [] }) ∷ 
      (record { name = "have-cheese" ; args = [] }) ∷ 
      (record { name = "have-crackers" ; args = [] }) ∷ 
      (record { name = "chips" ; args = (term "c1") ∷ [] }) ∷
      (record { name = "dip" ; args = (term "d1") ∷ [] }) ∷ 
      (record { name = "pop" ; args = (term "p1") ∷ [] }) ∷ 
      (record { name = "cheese" ; args = (term "z1") ∷ [] }) ∷
      (record { name = "crackers" ; args = (term "k1") ∷ [] }) ∷ []
  
  operators : List Operator
  operators = (record { label = "rewind-movie-2"; posPre = record { name = "counter-at-two-hours" ; args = [] } ∷ [] ; negPre = [] ; posPost = record { name = "movie-rewound" ; args = [] } ∷ [] ; negPost = [] }) ∷ 
              (record { label = "rewind-movie"; posPre = record { name = "counter-at-other-than-two-hours" ; args = [] } ∷ [] ; negPre = [] ; posPost = record { name = "movie-rewound" ; args = [] } ∷ [] ; negPost = record { name = "counter-at-zero" ; args = [] } ∷ [] }) ∷ 
              (record { label = "reset-counter"; posPre = [] ; negPre = [] ; posPost = record { name = "counter-at-zero" ; args = [] } ∷ [] ; negPost = [] }) ∷ 
              (record { label = "get-chips"; posPre = record { name = "chips" ; args = (var 0) ∷ [] } ∷ [] ; negPre = [] ; posPost = record { name = "have-chips" ; args = [] } ∷ [] ; negPost = [] }) ∷
              (record { label = "get-dip"; posPre = record { name = "dip" ; args = (var 0) ∷ [] } ∷ [] ; negPre = [] ; posPost = record { name = "have-dip" ; args = [] } ∷ [] ; negPost = [] }) ∷
              (record { label = "get-pop"; posPre = record { name = "pop" ; args = (var 0) ∷ [] } ∷ [] ; negPre = [] ; posPost = record { name = "have-pop" ; args = [] } ∷ [] ; negPost = [] }) ∷
              (record { label = "get-cheese"; posPre = record { name = "cheese" ; args = (var 0) ∷ [] } ∷ [] ; negPre = [] ; posPost = record { name = "have-cheese" ; args = [] } ∷ [] ; negPost = [] }) ∷
              (record { label = "get-crackers"; posPre = record { name = "crackers" ; args = (var 0) ∷ [] } ∷ [] ; negPre = [] ; posPost = record { name = "have-crackers" ; args = [] } ∷ [] ; negPost = [] }) ∷ []

  initialState : List Condition
  initialState = record { name = "chips" ; args = term "c1" ∷ [] } ∷ 
                  record { name = "dip" ; args = (term "d1") ∷ [] } ∷ 
                  record { name = "pop" ; args = term "p1" ∷ [] } ∷ 
                  record { name = "cheese" ; args = term "z1" ∷ [] } ∷ 
                  record { name = "crackers" ; args = term "k1" ∷ [] } ∷ 
                  record { name = "counter-at-other-than-two-hours" ; args = [] } ∷ []

  plan : Plan
  plan = record
    { label = "get-crackers"
    ; posPre =
        record { name = "crackers" ; args = term "k1" ∷ [] } ∷ []
    ; negPre = []
    ; posPost = record { name = "have-crackers" ; args = [] } ∷ []
    ; negPost = []
    }
    ∷ record
      { label = "get-cheese"
      ; posPre =
          record { name = "cheese" ; args = term "z1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-cheese" ; args = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "get-pop"
      ; posPre =
          record { name = "pop" ; args = term "p1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-pop" ; args = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "get-dip"
      ; posPre =
          record { name = "dip" ; args = term "d1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-dip" ; args = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "get-chips"
      ; posPre =
          record { name = "chips" ; args = term "c1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-chips" ; args = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "rewind-movie"
      ; posPre =
          record { name = "counter-at-other-than-two-hours" ; args = [] } ∷
          []
      ; negPre = []
      ; posPost = record { name = "movie-rewound" ; args = [] } ∷ []
      ; negPost = record { name = "counter-at-zero" ; args = [] } ∷ []
      }
    ∷ (record { label = "reset-counter"; posPre = [] ; negPre = [] ; posPost = record { name = "counter-at-zero" ; args = [] } ∷ [] ; negPost = [] } ∷ [])
  
  goals : Goal
  goals = record 
        { 
          pos = record { name = "movie-rewound" ; args = [] } ∷ 
                record { name = "counter-at-zero" ; args = [] } ∷ 
                record { name = "have-chips" ; args = [] } ∷ 
                (record { name = "have-dip" ; args = [] }) ∷ 
                (record { name = "have-pop" ; args = [] }) ∷ 
                (record { name = "have-cheese" ; args = [] }) ∷ 
                (record { name = "have-crackers" ; args = [] }) ∷ [] 
        ; neg = [] 
        }

  planProblem : PlanProblem
  planProblem = record
    { terms = term "c1" ∷ term "d1" ∷ term "p1" ∷ term "z1" ∷ term "k1" ∷ []
    ; conditions = conditions
    ; initialState = initialState
    ; operators = operators
    ; goals = goals
    }

  plan-is-valid : Solves initialState plan goals
  plan-is-valid = from-just (solver initialState plan goals)

  {-
    TRANSLATIONS 
  -}
  open import Translations.Translations
  open import ADJ.Core
  open import PrettyPrinter.PrettyPrinter 3000
  
  stateTrans : Vec (Prop × Mode) (Data.List.length conditions)
  stateTrans = translS initialState conditions

  operatorTrans : String
  operatorTrans = render (prettyProp (proj₁ (translO (Data.List.lookup operators (suc zero)))))

  goalTrans : String
  goalTrans = render (prettyProp (proj₁ (translG goals)))
