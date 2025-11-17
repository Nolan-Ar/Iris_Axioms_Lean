import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import IrisAxioms.iris_axioms_extended

namespace IrisGameTheory

open IrisAxiomsExtended

set_option linter.unusedVariables false

universe u v

/-- Jeu en forme normale :
    un ensemble d’agents et un espace de stratégies commun. -/
structure Game (Agent : Type u) (S : Type v) where
  payoff : Agent → (Agent → S) → ℝ

/-- Équilibre de Nash : aucun agent ne peut améliorer son payoff
    par une déviation unilatérale. -/
def NashEquilibrium {Agent : Type u} {S : Type v}
    [DecidableEq Agent] (G : Game Agent S) (s : Agent → S) : Prop :=
  ∀ a (s' : S),
    G.payoff a s ≥ G.payoff a (fun b => if b = a then s' else s b)

/-- Si, pour chaque agent, toute déviation unilatérale ne peut
    qu'affaiblir (ou laisser inchangé) son payoff, on a un équilibre de Nash. -/
theorem nash_of_best_responses {Agent : Type u} {S : Type v}
    [DecidableEq Agent] (G : Game Agent S) (s : Agent → S)
    (h : ∀ a (s' : S),
      G.payoff a (fun b => if b = a then s' else s b) ≤ G.payoff a s) :
    NashEquilibrium G s := by
  intro a s'
  specialize h a s'
  -- Grâce à la définition de ≥ comme "≤" inversé,
  -- le but est définitionnellement égal à `h`.
  simpa [NashEquilibrium] using h

-- Jeu du Revenu Universel (RU) :
-- les stratégies sont triviales (Unit),
-- le payoff ne dépend pas des stratégies, uniquement de l’allocation.

variable (Agent : Type u)

/-- Jeu du RU : chaque agent a une seule « stratégie » (Unit),
    et son payoff est simplement l’allocation qui lui est due. -/
def RUGame (U_t : ℝ) (alloc : Agent → ℝ) : Game Agent Unit where
  payoff a _ := alloc a

/-- Dans le jeu du RU, tout profil de stratégies est un équilibre de Nash,
    car les payoffs ne dépendent pas des stratégies. -/
theorem RUGame.nash_all_profiles [DecidableEq Agent]
    (U_t : ℝ) (alloc : Agent → ℝ) (s : Agent → Unit) :
    NashEquilibrium (RUGame Agent U_t alloc) s := by
  intro a s'
  -- Après développement, le but devient `alloc a ≥ alloc a`.
  have h : alloc a ≥ alloc a := le_rfl
  simp [RUGame]

/--
Lien direct avec l’axiome A12 :
la somme des payoffs (allocations) sur les bénéficiaires est exactement U_t.
-/
theorem RU_sum_preserved_as_game
    (U_t : ℝ) (beneficiaires : List CompteUtilisateur)
    (alloc : CompteUtilisateur → ℝ)
    (h_pos : ∀ cu ∈ beneficiaires, 0 ≤ alloc cu) :
    (beneficiaires.attach.map (fun ⟨cu,_⟩ => alloc cu)).sum = U_t := by
  -- C’est exactement A12_distribution_RU reformulé.
  exact A12_distribution_RU U_t beneficiaires alloc h_pos

end IrisGameTheory
