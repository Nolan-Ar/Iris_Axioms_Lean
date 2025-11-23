import Mathlib.Data.Option.Basic
import Mathlib.Tactic
import IrisAxioms.iris_axioms_extended

universe u v

namespace IrisIncompleteContracts

open IrisAxiomsExtended

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-- Potentially incomplete contract:
    for each state of the world ω we associate either a result, or nothing. -/
structure Contract (ω : Type u) (Outcome : Type v) where
  alloc : ω → Option Outcome

namespace Contract

variable {ω : Type u} {Outcome : Type v}

/-- A contract is complete if it specifies a result for every state. -/
def complete (c : Contract ω Outcome) : Prop :=
  ∀ s, c.alloc s ≠ none

/-- A contract is incomplete if at least one state remains unspecified. -/
def incomplete (c : Contract ω Outcome) : Prop :=
  ¬ complete c

/-- Refinement: c₂ extends c₁ without changing already defined outcomes. -/
def refines (c₁ c₂ : Contract ω Outcome) : Prop :=
  ∀ s o, c₁.alloc s = some o → c₂.alloc s = some o

lemma refines_refl (c : Contract ω Outcome) : refines c c := by
  intro s o h
  simpa using h

lemma refines_trans {c₁ c₂ c₃ : Contract ω Outcome}
    (h₁₂ : refines c₁ c₂) (h₂₃ : refines c₂ c₃) :
    refines c₁ c₃ := by
  intro s o h
  have h₂ : c₂.alloc s = some o := h₁₂ s o h
  exact h₂₃ s o h₂

/-- Completion of a contract by adding a default outcome
    to all previously unspecified states. -/
def completion (c : Contract ω Outcome) (default : Outcome) :
    Contract ω Outcome where
  alloc s :=
    match c.alloc s with
    | some o => some o
    | none   => some default

lemma completion_complete (c : Contract ω Outcome) (default : Outcome) :
    complete (completion c default) := by
  -- unfold the definition of `complete`
  intro s
  -- goal: (completion c default).alloc s ≠ none
  cases h : c.alloc s <;> simp [completion, h]

lemma refines_completion (c : Contract ω Outcome) (default : Outcome) :
    refines c (completion c default) := by
  intro s o h
  -- if c.alloc s = some o, then completion keeps the same outcome
  simp [completion, h]

end Contract

-- IRIS version of outcomes: variations (ΔV, ΔD) that respect
-- the thermodynamic constraint of non-negativity.

/-- IRIS-compatible outcome: non-negative variations of V and D. -/
structure IrisOutcome where
  ΔV : ℝ
  ΔD : ℝ
  h_nonneg : 0 ≤ ΔV ∧ 0 ≤ ΔD

/-- Any complete contract with IRIS outcomes provides, for each state,
    an outcome that is effectively non-negative in (V,D). -/
theorem exists_outcome_for_state
    {ω : Type u} (c : Contract ω IrisOutcome)
    (h_complete : Contract.complete c) (s : ω) :
    ∃ out, c.alloc s = some out ∧ 0 ≤ out.ΔV ∧ 0 ≤ out.ΔD := by
  have h_ne : c.alloc s ≠ none := h_complete s
  cases h : c.alloc s with
  | none =>
      -- Contradiction with contract completeness
      have : False := h_ne (by simp [h])
      exact this.elim
  | some out =>
      -- We retrieve the non-negativity built into IrisOutcome
      rcases out.h_nonneg with ⟨hΔV, hΔD⟩
      -- Goal: ∃ out, c.alloc s = some out ∧ 0 ≤ out.ΔV ∧ 0 ≤ out.ΔD
      refine ⟨out, ?_⟩
      -- We construct the nested conjunction
      simp [hΔV, hΔD]

end IrisIncompleteContracts
