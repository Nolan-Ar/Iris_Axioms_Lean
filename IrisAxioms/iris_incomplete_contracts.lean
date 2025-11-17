import Mathlib.Data.Option.Basic
import Mathlib.Tactic
import IrisAxioms.iris_axioms_extended

universe u v

namespace IrisIncompleteContracts

open IrisAxiomsExtended

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-- Contrat éventuellement incomplet :
    à chaque état du monde ω on associe soit un résultat, soit rien. -/
structure Contract (ω : Type u) (Outcome : Type v) where
  alloc : ω → Option Outcome

namespace Contract

variable {ω : Type u} {Outcome : Type v}

/-- Un contrat est complet s’il spécifie un résultat pour tout état. -/
def complete (c : Contract ω Outcome) : Prop :=
  ∀ s, c.alloc s ≠ none

/-- Un contrat est incomplet s’il reste au moins un état non spécifié. -/
def incomplete (c : Contract ω Outcome) : Prop :=
  ¬ complete c

/-- Raffinement : c₂ prolonge c₁ sans changer les issues déjà définies. -/
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

/-- Complétion d’un contrat en ajoutant une issue par défaut
    à tous les états auparavant non spécifiés. -/
def completion (c : Contract ω Outcome) (default : Outcome) :
    Contract ω Outcome where
  alloc s :=
    match c.alloc s with
    | some o => some o
    | none   => some default

lemma completion_complete (c : Contract ω Outcome) (default : Outcome) :
    complete (completion c default) := by
  -- unfold la définition de `complete`
  intro s
  -- but : (completion c default).alloc s ≠ none
  cases h : c.alloc s <;> simp [completion, h]

lemma refines_completion (c : Contract ω Outcome) (default : Outcome) :
    refines c (completion c default) := by
  intro s o h
  -- si c.alloc s = some o, alors la complétion garde la même issue
  simp [completion, h]

end Contract

-- Version IRIS des résultats : variations (ΔV, ΔD) qui respectent
-- la contrainte thermodynamique de non-négativité.

/-- Issue compatible avec IRIS : variations non négatives de V et D. -/
structure IrisOutcome where
  ΔV : ℝ
  ΔD : ℝ
  h_nonneg : 0 ≤ ΔV ∧ 0 ≤ ΔD

/-- Tout contrat complet à issues IRIS fournit, pour chaque état,
    une issue effectivement non négative en (V,D). -/
theorem exists_outcome_for_state
    {ω : Type u} (c : Contract ω IrisOutcome)
    (h_complete : Contract.complete c) (s : ω) :
    ∃ out, c.alloc s = some out ∧ 0 ≤ out.ΔV ∧ 0 ≤ out.ΔD := by
  have h_ne : c.alloc s ≠ none := h_complete s
  cases h : c.alloc s with
  | none =>
      -- Contradiction avec la complétude du contrat
      have : False := h_ne (by simp [h])
      exact this.elim
  | some out =>
      -- On récupère la non-négativité intégrée dans IrisOutcome
      rcases out.h_nonneg with ⟨hΔV, hΔD⟩
      -- But : ∃ out, c.alloc s = some out ∧ 0 ≤ out.ΔV ∧ 0 ≤ out.ΔD
      refine ⟨out, ?_⟩
      -- On construit la conjonction imbriquée
      simp [hΔV, hΔD]

end IrisIncompleteContracts
