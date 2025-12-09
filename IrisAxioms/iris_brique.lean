/-
  Closed Contracts Theorem
  Groups several fundamental IRIS guarantees:
  - inviolability of transactions,
  - effective UBI distribution,
  - value conservation.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import IrisAxioms.iris_axioms

open IrisAxioms

namespace IrisTheoremes

/--
Closed contracts theorem:
simple grouping of three key IRIS axioms.
-/
theorem contrat_clos :
    -- Inviolability of transactions
    (∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx) ∧
    -- Effective UBI distribution
    (∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
        (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
        (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t) ∧
    -- Fundamental value conservation
    (∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D) := by
  constructor
  · exact A3_inviolabilite_transactions
  constructor
  · intro U_t beneficiaires alloc h_pos
    exact A12_distribution_RU U_t beneficiaires alloc h_pos
  · intro v
    exact T_conservation_thermodynamique_valeurs v

/-- Transactions are always valid and signed. -/
theorem transactions_toujours_valides :
    ∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx :=
  (contrat_clos).left

/-- Universal basic income is always fully distributed. -/
theorem RU_toujours_distribue :
    ∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
      (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
      (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t :=
  (contrat_clos).right.left

/-- Living value and liability D remain non-negative. -/
theorem valeurs_toujours_positives :
    ∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D :=
  (contrat_clos).right.right

/--
Extended version that adds two other axioms:
- absence of debt emission,
- strict exclusion of U from enterprise accounts.
-/
theorem contrat_clos_etendu :
    -- Basic inviolability
    (∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx) ∧
    -- Effective distribution
    (∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
        (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
        (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t) ∧
    -- Fundamental conservation
    (∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D) ∧
    -- Absence of debt emission
    (∀ (U_t V_on ρ : ℝ) (T N : ℕ),
        (0 ≤ ρ ∧ ρ ≤ 0.3) → (0 < T ∧ 0 < N) → 0 ≤ V_on →
        U_t = (1 - ρ) * V_on / ((T : ℝ) * (N : ℝ)) ∧ 0 ≤ U_t) ∧
    -- Strict exclusion of U for enterprises
    (∀ (ce : CompteEntreprise), 0 ≤ ce.tresorerie_V) := by
  constructor
  · exact A3_inviolabilite_transactions
  constructor
  · exact A12_distribution_RU
  constructor
  · intro v
    exact T_conservation_thermodynamique_valeurs v
  constructor
  · exact A2_absence_emission_dette
  · exact T_exclusion_U_entreprise

end IrisTheoremes
