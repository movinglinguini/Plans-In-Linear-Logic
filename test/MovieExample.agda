open import Data.List
open import Data.Vec
open import Data.Irrelevant
open import Data.Maybe
open import Data.Fin
open import Data.Product
open import Data.String

open import STRIPS.Problem

module MovieExample where
  conditions : List (Condition 0)
  conditions = (record { name = "movie-rewound" ; terms = [] }) ∷
      (record { name = "counter-at-two-hours" ; terms = [] }) ∷ 
      (record { name = "counter-at-other-than-two-hours" ; terms = [] }) ∷ 
      (record { name = "counter-at-zero" ; terms = [] }) ∷ 
      (record { name = "have-chips" ; terms = [] }) ∷ 
      (record { name = "have-dip" ; terms = [] }) ∷ 
      (record { name = "have-pop" ; terms = [] }) ∷ 
      (record { name = "have-cheese" ; terms = [] }) ∷ 
      (record { name = "have-crackers" ; terms = [] }) ∷ 
      (record { name = "chips" ; terms = (const "c1") ∷ [] }) ∷
      (record { name = "dip" ; terms = (const "d1") ∷ [] }) ∷ 
      (record { name = "pop" ; terms = (const "p1") ∷ [] }) ∷ 
      (record { name = "cheese" ; terms = (const "z1") ∷ [] }) ∷
      (record { name = "crackers" ; terms = (const "k1") ∷ [] }) ∷ []
  
  operators : List Operator
  operators = (record { label = "rewind-movie-2"; arity = 0; posPre = record { name = "counter-at-two-hours" ; terms = [] } ∷ [] ; negPre = [] ; posPost = record { name = "movie-rewound" ; terms = [] } ∷ [] ; negPost = [] }) ∷ 
              (record { label = "rewind-movie"; arity = 0; posPre = record { name = "counter-at-other-than-two-hours" ; terms = [] } ∷ [] ; negPre = [] ; posPost = record { name = "movie-rewound" ; terms = [] } ∷ [] ; negPost = record { name = "counter-at-zero" ; terms = [] } ∷ [] }) ∷ 
              (record { label = "reset-counter"; arity = 0; posPre = [] ; negPre = [] ; posPost = record { name = "counter-at-zero" ; terms = [] } ∷ [] ; negPost = [] }) ∷ 
              (record { 
                label = "get-chips"; 
                arity = 1 ;
                posPre = record { name = "chips" ; terms = (var zero) ∷ [] } ∷ [] ; 
                negPre = [] ; 
                posPost = record { name = "have-chips" ; terms = [] } ∷ [] ; 
                negPost = [] }) ∷
              (record { label = "get-dip";
                        arity = 1 ;
                        posPre = record { name = "dip" ; terms = (var zero) ∷ [] } ∷ [] ;
                        negPre = [] ;
                        posPost = record { name = "have-dip" ; terms = [] } ∷ [] ; negPost = [] }) ∷
              (record { label = "get-pop";
                        arity = 1 ;
                        posPre = record { name = "pop" ; terms = (var zero) ∷ [] } ∷ [] ;
                        negPre = [] ;
                        posPost = record { name = "have-pop" ; terms = [] } ∷ [] ;
                        negPost = [] }) ∷
              (record { label = "get-cheese";
                        arity = 1 ;
                        posPre = record { name = "cheese" ; terms = (var zero) ∷ [] } ∷ [] ;
                        negPre = [] ;
                        posPost = record { name = "have-cheese" ; terms = [] } ∷ [] ;
                        negPost = [] }) ∷
              (record { label = "get-crackers" ;
                        arity = 1 ;
                        posPre = record { name = "crackers" ; terms = (var zero) ∷ [] } ∷ [] ;
                        negPre = [] ;
                        posPost = record { name = "have-crackers" ; terms = [] } ∷ [] ;
                        negPost = [] }) ∷ []

  initialState : List (Condition 0)
  initialState = record { name = "chips" ; terms = const "c1" ∷ [] } ∷ 
                  record { name = "dip" ; terms = (const "d1") ∷ [] } ∷ 
                  record { name = "pop" ; terms = const "p1" ∷ [] } ∷ 
                  record { name = "cheese" ; terms = const "z1" ∷ [] } ∷ 
                  record { name = "crackers" ; terms = const "k1" ∷ [] } ∷ 
                  record { name = "counter-at-other-than-two-hours" ; terms = [] } ∷ []

  plan : Plan
  plan = record
    { label = "get-crackers"
    ; posPre =
        record { name = "crackers" ; terms = const "k1" ∷ [] } ∷ []
    ; negPre = []
    ; posPost = record { name = "have-crackers" ; terms = [] } ∷ []
    ; negPost = []
    }
    ∷ record
      { label = "get-cheese"
      ; posPre =
          record { name = "cheese" ; terms = const "z1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-cheese" ; terms = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "get-pop"
      ; posPre =
          record { name = "pop" ; terms = const "p1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-pop" ; terms = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "get-dip"
      ; posPre =
          record { name = "dip" ; terms = const "d1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-dip" ; terms = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "get-chips"
      ; posPre =
          record { name = "chips" ; terms = const "c1" ∷ [] } ∷ []
      ; negPre = []
      ; posPost = record { name = "have-chips" ; terms = [] } ∷ []
      ; negPost = []
      }
    ∷ record
      { label = "rewind-movie"
      ; posPre =
          record { name = "counter-at-other-than-two-hours" ; terms = [] } ∷
          []
      ; negPre = []
      ; posPost = record { name = "movie-rewound" ; terms = [] } ∷ []
      ; negPost = record { name = "counter-at-zero" ; terms = [] } ∷ []
      }
    ∷ (record { label = "reset-counter"; posPre = [] ; negPre = [] ; posPost = record { name = "counter-at-zero" ; terms = [] } ∷ [] ; negPost = [] } ∷ [])
  
  goals : Goal
  goals = record 
        { 
          pos = record { name = "movie-rewound" ; terms = [] } ∷ 
                record { name = "counter-at-zero" ; terms = [] } ∷ 
                record { name = "have-chips" ; terms = [] } ∷ 
                (record { name = "have-dip" ; terms = [] }) ∷ 
                (record { name = "have-pop" ; terms = [] }) ∷ 
                (record { name = "have-cheese" ; terms = [] }) ∷ 
                (record { name = "have-crackers" ; terms = [] }) ∷ [] 
        ; neg = [] 
        }

  planProblem : PlanProblem
  planProblem = record
    { terms = const "c1" ∷ const "d1" ∷ const "p1" ∷ const "z1" ∷ const "k1" ∷ []
    ; conditions = conditions
    ; initialState = initialState
    ; operators = operators
    ; goals = goals
    }

  {-
    TRANSLATIONS 
  -}
  open import Translations.Translations
  open import ADJ.Core
  open import PrettyPrinter.PrettyPrinter 3000
  
  pProblem : String
  pProblem = render (prettyProblem (translProb planProblem))
