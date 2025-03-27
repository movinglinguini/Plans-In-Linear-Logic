open import Data.List
open import Data.Vec
open import Data.Irrelevant
open import Data.Maybe
open import Data.Fin
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.String
open import Data.Bool
open import Data.Vec.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality

open import STRIPS.Problem

module BlocksWorld where
  labels : List String
  labels = "on" ∷ "on-table" ∷ "clear" ∷ "handempty" ∷ "holding" ∷ []

  -- Problem conditions
  conditions : List GroundCondition
  conditions = (record { label = "clear" ; terms = const "A" ∷ [] }) 
    ∷ (record { label = "clear" ; terms = const "B" ∷ [] }) 
    ∷ (record { label = "clear" ; terms = const "C" ∷ [] })
    ∷ (record { label = "on" ; terms = const "A" ∷ const "B" ∷ [] })
    ∷ (record { label = "on" ; terms = const "A" ∷ const "C" ∷ [] })
    ∷ (record { label = "on" ; terms = const "B" ∷ const "A" ∷ [] })
    ∷ (record { label = "on" ; terms = const "B" ∷ const "C" ∷ [] })
    ∷ (record { label = "on" ; terms = const "C" ∷ const "A" ∷ [] })
    ∷ (record { label = "on" ; terms = const "C" ∷ const "B" ∷ [] }) 
    ∷ (record { label = "handempty" ; terms = [] })
    ∷ (record { label = "on-table" ; terms = const "A" ∷ [] })
    ∷ (record { label = "on-table" ; terms = const "B" ∷ [] })
    ∷ (record { label = "on-table" ; terms = const "C" ∷ [] })
    ∷ (record { label = "holding" ; terms = const "A" ∷ [] })
    ∷ (record { label = "holding" ; terms = const "B" ∷ [] })
    ∷ (record { label = "holding" ; terms = const "C" ∷ [] })
    ∷ []

  -- Problem operators
  operators : List Operator
  operators = 
    record { label = "pick-up" ; arity = 1 
            ; conds =
              -- Preconditions
              opcond ⟨ (record { label = "clear" ; terms = (var zero) ∷ [] }) , true ⟩ precond
              ∷ opcond ⟨ (record { label = "on-table" ; terms = var zero ∷ [] }) , true ⟩ precond
              ∷ opcond ⟨ (record { label = "handempty" ; terms = [] }) , true ⟩ precond
              -- Postconditions 
              ∷ opcond ⟨ (record { label = "on-table" ; terms = (var zero) ∷ [] }) , false ⟩ postcond 
              ∷ opcond ⟨ (record { label = "clear" ; terms = (var zero) ∷ [] }) , false ⟩ postcond 
              ∷ opcond ⟨ (record { label = "handempty" ; terms = [] }) , true ⟩ postcond
              ∷ [] 
            }
    ∷ record { label = "put-down" ; arity = 1 
              ; conds = 
                  -- Preconditions
                  opcond ⟨ (record { label = "holding" ; terms = var zero ∷ [] }) , true ⟩ precond 
                  -- Postconditions
                  ∷ opcond ⟨ (record { label = "holding" ; terms = var zero ∷ [] }) , false ⟩ postcond
                  ∷ opcond ⟨ (record { label = "clear" ; terms = var zero ∷ [] }) , true ⟩ postcond
                  ∷ opcond ⟨ (record { label = "handempty" ; terms = [] }) , true ⟩ postcond
                  ∷ opcond ⟨ (record { label = "on-table" ; terms = var zero ∷ [] }) , true ⟩ postcond
                  ∷ []
              }
    ∷ record { label = "stack" ; arity = 2 
              ; conds = 
                -- Preconditions
                opcond ⟨ (record { label = "holding" ; terms = (var zero) ∷ [] }) , true ⟩ precond 
                ∷ opcond ⟨ record { label = "clear" ; terms = var (suc zero) ∷ [] } , true ⟩ precond
                -- Postconditions 
                ∷ opcond ⟨ (record { label = "holding" ; terms = var zero ∷ [] }) , false ⟩ postcond
                ∷ opcond ⟨ (record { label = "clear" ; terms = var (suc zero) ∷ [] }) , false ⟩ postcond
                ∷ opcond ⟨ (record { label = "clear" ; terms = var zero ∷ [] }) , true ⟩ postcond
                ∷ opcond ⟨ (record { label = "handempty" ; terms = [] }) , true ⟩ postcond
                ∷ opcond ⟨ (record { label = "on" ; terms = (var zero) ∷ (var (suc zero)) ∷ [] }) , true ⟩ postcond
                ∷ []
              }
    ∷ record { label = "unstack" ; arity = 2 
              ; conds = 
                -- Preconditions
                opcond ⟨ (record { label = "on" ; terms = var zero ∷ var (suc zero) ∷ [] }) , true ⟩ precond 
                ∷ opcond ⟨ (record { label = "clear" ; terms = var zero ∷ [] }) , true ⟩ precond
                ∷ opcond ⟨ (record { label = "handempty" ; terms = [] }) , true ⟩ precond
                -- Postconditions
                ∷ opcond ⟨ (record { label = "holding" ; terms = var zero ∷ [] }) , true ⟩ postcond
                ∷ opcond ⟨ (record { label = "clear" ; terms = var (suc zero) ∷ [] }) , true ⟩ postcond
                ∷ opcond ⟨ (record { label = "clear" ; terms = var zero ∷ [] }) , false ⟩ postcond
                ∷ opcond ⟨ (record { label = "handempty" ; terms = [] }) , false ⟩ postcond
                ∷ opcond ⟨ (record { label = "on" ; terms = var zero ∷ var (suc zero) ∷ [] }) , false ⟩ postcond
                ∷ []
              }
    ∷ []  

  -- Initial state
  initState : List GroundCondition
  initState = record { label = "clear" ; terms = const "C" ∷ [] }
    ∷ record { label = "clear" ; terms = const "A" ∷ [] }
    ∷ record { label = "on" ; terms = const "A" ∷ const "B" ∷ [] }
    ∷ record { label = "on-table" ; terms = const "C" ∷ [] }
    ∷ record { label = "on-table" ; terms = const "B" ∷ [] }
    ∷ record { label = "handempty" ; terms = [] }
    ∷ []

  -- Proof that the initial state is well-formed
  initState-wf : State initState (Data.Vec.fromList conditions)
  initState-wf = from-just (maybeWfState initState ((Data.Vec.fromList conditions)))

  -- Goals
  goalConds : List (GroundCondition × Bool)
  goalConds = ⟨ (record { label = "on" ; terms = const "C" ∷ const "B" ∷ [] }) , true ⟩ 
    ∷ ⟨ (record { label = "on-table" ; terms = const "A" ∷ [] }) , true ⟩
    ∷ []
  
  goal : Goals goalConds (Data.Vec.fromList conditions)
  goal = from-just (maybeGoal goalConds (Data.Vec.fromList conditions))

  -- The problem statement
  problem : PlanProblem (Data.Vec.fromList conditions) initState (Data.Vec.fromList operators) goal
  problem = wf/prob (Data.Vec.fromList conditions) initState (Data.Vec.fromList operators) goal initState-wf

  -- Transitions for a plan