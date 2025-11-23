import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import IrisAxioms.iris_axioms_extended

namespace IrisGameTheory

open IrisAxiomsExtended

set_option linter.unusedVariables false

universe u v

/-- Normal-form game:
    a set of agents and a common strategy space. -/
structure Game (Agent : Type u) (S : Type v) where
  payoff : Agent → (Agent → S) → ℝ

/-- Nash equilibrium: no agent can improve their payoff
    by a unilateral deviation. -/
def NashEquilibrium {Agent : Type u} {S : Type v}
    [DecidableEq Agent] (G : Game Agent S) (s : Agent → S) : Prop :=
  ∀ a (s' : S),
    G.payoff a s ≥ G.payoff a (fun b => if b = a then s' else s b)

/-- If, for each agent, any unilateral deviation can only
    weaken (or leave unchanged) their payoff, we have a Nash equilibrium. -/
theorem nash_of_best_responses {Agent : Type u} {S : Type v}
    [DecidableEq Agent] (G : Game Agent S) (s : Agent → S)
    (h : ∀ a (s' : S),
      G.payoff a (fun b => if b = a then s' else s b) ≤ G.payoff a s) :
    NashEquilibrium G s := by
  intro a s'
  specialize h a s'
  -- Thanks to the definition of ≥ as "≤" reversed,
  -- the goal is definitionally equal to `h`.
  simpa [NashEquilibrium] using h

-- Universal Basic Income (UBI) game:
-- strategies are trivial (Unit),
-- payoff does not depend on strategies, only on allocation.

variable (Agent : Type u)

/-- UBI game: each agent has a single "strategy" (Unit),
    and their payoff is simply the allocation they are due. -/
def RUGame (U_t : ℝ) (alloc : Agent → ℝ) : Game Agent Unit where
  payoff a _ := alloc a

/-- In the UBI game, every strategy profile is a Nash equilibrium,
    because payoffs do not depend on strategies. -/
theorem RUGame.nash_all_profiles [DecidableEq Agent]
    (U_t : ℝ) (alloc : Agent → ℝ) (s : Agent → Unit) :
    NashEquilibrium (RUGame Agent U_t alloc) s := by
  intro a s'
  -- After expansion, the goal becomes `alloc a ≥ alloc a`.
  have h : alloc a ≥ alloc a := le_rfl
  simp [RUGame]

/--
Direct link to axiom A12:
the sum of payoffs (allocations) over beneficiaries is exactly U_t.
-/
theorem RU_sum_preserved_as_game
    (U_t : ℝ) (beneficiaires : List CompteUtilisateur)
    (alloc : CompteUtilisateur → ℝ)
    (h_pos : ∀ cu ∈ beneficiaires, 0 ≤ alloc cu) :
    (beneficiaires.attach.map (fun ⟨cu,_⟩ => alloc cu)).sum = U_t := by
  -- This is exactly A12_distribution_RU reformulated.
  exact A12_distribution_RU U_t beneficiaires alloc h_pos

end IrisGameTheory
