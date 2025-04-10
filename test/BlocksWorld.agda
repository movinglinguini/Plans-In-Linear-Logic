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
open import Translations.Translations
open import ADJ.Core
open import PrettyPrinter.PrettyPrinter 3000

module BlocksWorld where
  terms : List TermConstant
  terms = const "A" ∷ const "B" ∷ const "C" ∷ []

  terms-vec = Data.Vec.fromList terms

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

  conds-vec = Data.Vec.fromList conditions

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
              ∷ opcond ⟨ (record { label = "handempty" ; terms = [] }) , false ⟩ postcond
              ∷ opcond ⟨ (record { label = "holding" ; terms = var zero ∷ [] }) , true ⟩ postcond
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
  
  op-vec = Data.Vec.fromList operators

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
  initState-wf : State initState (conds-vec)
  initState-wf = from-just (maybeWfState initState (conds-vec))

  -- Proof that the condition list is well-formed
  conds-wf : WfGroundConditions conds-vec terms-vec
  conds-wf = from-just (maybeWfConditions conds-vec terms-vec)

  -- Goals
  goalConds : List (GroundCondition × Bool)
  goalConds = ⟨ (record { label = "on" ; terms = const "C" ∷ const "B" ∷ [] }) , true ⟩ 
    ∷ ⟨ (record { label = "on-table" ; terms = const "A" ∷ [] }) , true ⟩
    ∷ []
  
  goal : Goals goalConds (conds-vec)
  goal = from-just (maybeGoal goalConds (Data.Vec.fromList conditions))

  -- A well-formed problem statement.
  problem : PlanProblem terms-vec conds-vec initState op-vec goal
  problem = wf/prob terms-vec conds-vec initState op-vec goal conds-wf initState-wf

  {- 
    Transitions for a plan. The transitions are

    - unstack A B
    - put-down A
    - pick-up C
    - stack C B
  -}
  transitions : List (Transition conds-vec op-vec)
  transitions =
    wf/transition (from-just (findByLabel "unstack" operators)) (const "A" ∷ const "B" ∷ []) (there (there (there (here refl)))) (wf/groundop/s
       (wf/groundop/s
        (wf/groundop/s
         (wf/groundop/s
          (wf/groundop/s
           (wf/groundop/s
            (wf/groundop/s
             (wf/groundop/s wf/groundop/z (there (there (there (here refl)))))
             (there
              (there
               (there
                (there (there (there (there (there (there (here refl)))))))))))
            (here refl))
           (there (here refl)))
          (there
           (there
            (there
             (there
              (there
               (there
                (there
                 (there (there (there (there (there (there (here refl)))))))))))))))
         (there
          (there
           (there
            (there (there (there (there (there (there (here refl)))))))))))
        (here refl))
       (there (there (there (here refl)))))
    ∷ wf/transition (from-just (findByLabel "put-down" operators)) (const "A" ∷ []) (there (here refl)) (wf/groundop/s
       (wf/groundop/s
        (wf/groundop/s
         (wf/groundop/s
          (wf/groundop/s wf/groundop/z
           (there
            (there
             (there
              (there
               (there (there (there (there (there (there (here refl))))))))))))
          (there
           (there
            (there
             (there (there (there (there (there (there (here refl)))))))))))
         (here refl))
        (there
         (there
          (there
           (there
            (there
             (there
              (there
               (there (there (there (there (there (there (here refl)))))))))))))))
       (there
        (there
         (there
          (there
           (there
            (there
             (there
              (there (there (there (there (there (there (here refl)))))))))))))))
    ∷ wf/transition (from-just (findByLabel "pick-up" operators)) (const "C" ∷ []) (here refl) (wf/groundop/s (wf/groundop/s
       (wf/groundop/s
        (wf/groundop/s
         (wf/groundop/s
          (wf/groundop/s
           (wf/groundop/s wf/groundop/z
            (there
             (there
              (there
               (there
                (there
                 (there
                  (there
                   (there
                    (there
                     (there
                      (there (there (there (there (there (here refl)))))))))))))))))
           (there
            (there
             (there
              (there (there (there (there (there (there (here refl)))))))))))
          (there (there (here refl))))
         (there
          (there
           (there
            (there
             (there
              (there
               (there (there (there (there (there (there (here refl))))))))))))))
        (there
         (there
          (there
           (there (there (there (there (there (there (here refl)))))))))))
       (there
        (there
         (there
          (there
           (there
            (there
             (there (there (there (there (there (there (here refl)))))))))))))) (there (there (here refl))))
    ∷ wf/transition (from-just (findByLabel "stack" operators)) (const "C" ∷ const "B" ∷ []) (there (there (here refl))) (wf/groundop/s
       (wf/groundop/s
        (wf/groundop/s
         (wf/groundop/s
          (wf/groundop/s
           (wf/groundop/s
            (wf/groundop/s wf/groundop/z
             (there
              (there
               (there (there (there (there (there (there (here refl))))))))))
            (there
             (there
              (there
               (there (there (there (there (there (there (here refl)))))))))))
           (there (there (here refl))))
          (there (here refl)))
         (there
          (there
           (there
            (there
             (there
              (there
               (there
                (there
                 (there
                  (there
                   (there (there (there (there (there (here refl)))))))))))))))))
        (there (here refl)))
       (there
        (there
         (there
          (there
           (there
            (there
             (there
              (there
               (there
                (there
                 (there (there (there (there (there (here refl)))))))))))))))))
    ∷ []

  -- Should normalize to just a large data structure that tells us
  -- this plan is well-formed.
  plan : Plan initState-wf goal
  plan = from-just (solver-plan initState-wf goal transitions)

  -- Not only is the plan well-formed, but it also 
  -- solves the problem.
  plan-solves-problem : Solves problem plan
  plan-solves-problem = solves problem plan

  {- 
    Translating the planning problem
  -}
  transl-prob = translProb problem
  transl-prob-pretty = render (prettyProblem transl-prob)
