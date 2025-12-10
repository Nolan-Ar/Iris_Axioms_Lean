import IrisAxioms.iris_axioms_extended
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open IrisAxiomsExtended

namespace IrisTheoremesExtended

set_option linter.unusedVariables false

/-!
# IRIS — Extended Theorems

This file contains the original theorems and 15+ new theorems
derived from the extended axioms A1-A27.

## Organization:
- Section 1: Original theorems (closed contract, etc.)
- Section 2: Conservation Theorems (T1-T2)
- Section 3: Stability Theorems (T3-T4)
- Section 4: Equity Theorems (T5-T6)
- Section 5: Security Theorems (T7-T8)
- Section 6: Resilience Theorems (T9-T10)
- Section 7: Circulation Theorems (T11-T13)
- Section 8: Thermodynamic Theorems (T14-T16)

## Proof Strategies Documentation

This section explains the main proof techniques used throughout the file.

### 1. Direct Axiom Application
**Pattern**: Directly apply an axiom to prove the goal
**Example**: `T1_conservation_globale_init` uses `A13_neutralite_initiale`
**When to use**: Goal matches exactly an axiom conclusion

### 2. Constructive Existence Proofs
**Pattern**: Construct explicit witness to prove `∃ x, P(x)`
**Example**: `T4_etat_stationnaire_possible` constructs a SystemState
**Tactics used**: `refine ⟨witness, ?_, ?_⟩`, `simpa`
**When to use**: Need to show existence by example

### 3. Inequality Chains with `linarith`
**Pattern**: Prove inequalities using linear arithmetic
**Example**: Conservation proofs that manipulate bounds
**Tactics used**: `linarith`, `calc`, `norm_num`
**When to use**: Dealing with numeric constraints, bounds

### 4. Case Analysis
**Pattern**: Split proof by cases on a condition
**Example**: Checking thermometer zones (cold/equilibrium/hot)
**Tactics used**: `by_cases`, `rcases`, `cases`
**When to use**: Proof depends on different scenarios

### 5. Contradiction Proofs
**Pattern**: Assume negation and derive false
**Example**: Proving no double-spend by contradiction
**Tactics used**: `by_contra`, `intro`, `linarith`
**When to use**: Easier to show impossibility than direct proof

### 6. Ring/Field Normalization
**Pattern**: Simplify algebraic expressions
**Example**: Proving conservation equations hold
**Tactics used**: `ring`, `ring_nf`, `field_simp`
**When to use**: Goals involve polynomial/rational expressions

### 7. Structural Decomposition
**Pattern**: Break down compound structures
**Example**: Extract components from CompteUtilisateur
**Tactics used**: `rcases`, `obtain`, `have`
**When to use**: Working with complex data structures

### 8. Substitution and Rewriting
**Pattern**: Replace equal terms using hypotheses
**Example**: Using conservation to substitute values
**Tactics used**: `rw`, `subst`, `simp [hyp]`
**When to use**: Need to use equalities to transform goal

## Common Proof Patterns in IRIS

### Pattern 1: Positivity from Structure Invariants
```lean
theorem value_positive (v : Valeurs) : 0 ≤ v.V := v.hV
-- Direct use of structure invariant hV
```

### Pattern 2: Conservation Manipulation
```lean
-- Start with: S + U + V + D = 0
-- Derive: V = -(S + U + D)
-- Technique: Algebraic manipulation + linarith
```

### Pattern 3: Thermometer Zone Checking
```lean
-- Check: r_t = D_total / V_on_total
-- Compare with thresholds: 0.85, 1.15
-- Technique: unfold thermometre, norm_num
```

### Pattern 4: List Sum Properties
```lean
-- For UBI distribution: (beneficiaires.map alloc).sum = U_t
-- Technique: Use A12 axiom directly
```

-/

/-! # Section 1: ORIGINAL THEOREMS (REMINDER)

  We redefine here some basic theorems, placing them
  in the extended namespace to be able to reuse them.
-/

/-! ## Closed contract (extended version)

  This theorem groups:
  - inviolability of transactions (A3)
  - complete distribution of UBI (A12)
  - positivity of V and D (A10)
-/
theorem contrat_clos :
    (∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx) ∧
    (∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
        (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
          (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t) ∧
      (∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D) := by
  constructor
  · -- Inviolability of transactions
    intro cu tx
    exact A3_inviolabilite_transactions cu tx
  constructor
  · -- Complete distribution of UBI
    intro U_t beneficiaires alloc h_pos
    exact A12_distribution_RU U_t beneficiaires alloc h_pos
  · -- Positivity of V and D
    intro v
    exact T_conservation_thermodynamique_valeurs v

/-! # Section 2: CONSERVATION THEOREMS (T1-T2) -/

/-! ## T1: Global conservation at initialization

  At initialization, the sum of actual values recorded
  by the oracle is equal to the corresponding total debt.
-/
theorem T1_conservation_globale_init (oracle : Oracle) :
    let V_init := (oracle.biens_enregistres.map (·.valeur_effective)).sum
    let D_init := V_init
    V_init = D_init := by
  exact A13_neutralite_initiale oracle

/-! ## T1bis: Wealth conservation

  Total wealth is the sum of on-chain value and immobilized value.
-/
theorem T1bis_conservation_patrimoine (sys : SystemState) :
    sys.V_total = sys.V_on + sys.V_immo :=
  A27_conservation_patrimoine sys

/-! ## T2: No ex-nihilo monetary creation

  The value variation ΔV created from energy is always ≥ 0.
-/
theorem T2_pas_creation_monetaire
    (η_phys μ_social Δt w_S w_U S_burn U_burn : ℝ)
    (h_phys : 0 < η_phys ∧ η_phys ≤ 1)
    (h_social : 1 ≤ μ_social ∧ μ_social ≤ 2)
    (h_convexe : w_S + w_U = 1 ∧ 0 ≤ w_S ∧ 0 ≤ w_U)
    (h_burn : 0 ≤ S_burn ∧ 0 ≤ U_burn)
    (h_dt : 0 < Δt) :
    let η := η_phys * μ_social
    let E := w_S * S_burn + w_U * U_burn
    let ΔV := η * Δt * E
    0 ≤ ΔV := by
  exact A6_creation_valeur_energetique η_phys μ_social Δt w_S w_U S_burn U_burn
    h_phys h_social h_convexe h_burn h_dt

/-! # Section 3: STABILITY THEOREMS (T3-T4) -/

/-! ## T3: Thermometer in equilibrium zone

  If the ratio r_t = D_total / V_on_total is in [0.85, 1.15],
  then the system is considered thermodynamically stable.
-/
theorem T3_thermometre_equilibre (rad : RAD)
    (h_stable : 0.85 ≤ thermometre rad ∧ thermometre rad ≤ 1.15) :
    let r_t := thermometre rad
    0.85 ≤ r_t ∧ r_t ≤ 1.15 := by
  exact h_stable

/-! ## T4: Existence of a stationary state

  **PROOF STRATEGY**: Constructive existence proof

  **Goal**: Prove ∃ sys : SystemState, [properties hold]

  **Approach**:
  1. Construct explicit witness (concrete SystemState)
  2. Verify each property holds for the witness
  3. Use `refine ⟨witness, proof1, proof2, proof3⟩` pattern

  **Key insight**: Rather than prove abstract existence,
  we show a realistic example satisfying all constraints.

  Properties to verify:
  - V_total ≥ 0 (economic value is non-negative)
  - D_total ≥ 0 (debt is non-negative)
  - V_total = V_on + V_immo (A2 decomposition)
-/
theorem T4_etat_stationnaire_possible :
    ∃ sys : SystemState, sys.V_total ≥ 0 ∧ sys.D_total ≥ 0 ∧ sys.V_total = sys.V_on + sys.V_immo := by
  -- STEP 1: Construct a concrete witness
  -- We create a realistic economic state:
  --   - 1M total value (V_total)
  --   - 1M corresponding debt (D_total) - thermodynamic mirror
  --   - 700k circulating (V_on) - 70% liquidity
  --   - 300k immobilized (V_immo) - 30% in patrimony
  let sys : SystemState :=
    { utilisateurs := []         -- Empty for simplicity (not needed for this proof)
      entreprises := []          -- Empty for simplicity
      V_total := 1000000         -- 1M€ total value
      D_total := 1000000         -- Mirrors V_total in equilibrium
      V_on := 700000             -- 700k€ in circulation
      V_immo := 300000           -- 300k€ immobilized (V_on + V_immo = V_total)
      cycle_actuel := 42         -- Arbitrary cycle number
      h_conservation := by norm_num  -- Verify 1000000 = 700000 + 300000
      h_V := by norm_num         -- Verify 0 ≤ 1000000
      h_D := by norm_num         -- Verify 0 ≤ 1000000
      h_V_on := by norm_num      -- Verify 0 ≤ 700000
      h_V_immo := by norm_num }  -- Verify 0 ≤ 300000

  -- STEP 2: Prove the witness satisfies all three properties
  -- Using `refine` to provide witness and create three subgoals
  refine ⟨sys, ?_, ?_, ?_⟩

  -- Subgoal 1: V_total ≥ 0
  -- TECHNIQUE: Use structure invariant sys.h_V
  · simpa using sys.h_V

  -- Subgoal 2: D_total ≥ 0
  -- TECHNIQUE: Use structure invariant sys.h_D
  · simpa using sys.h_D

  -- Subgoal 3: V_total = V_on + V_immo
  -- TECHNIQUE: Use conservation property sys.h_conservation
  -- This was verified at construction time via norm_num
  · simpa using sys.h_conservation

/-! # Section 4: EQUITY THEOREMS (T5-T6) -/

/-! ## T5: No impoverishment by UBI

  The universal basic income U_t is always positive or zero.
-/
theorem T5_non_appauvrissement
    (U_t V_on ρ : ℝ) (T N : ℕ)
    (h_rho : 0 ≤ ρ ∧ ρ ≤ 0.3)
    (h_params : 0 < T ∧ 0 < N)
    (h_V : 0 ≤ V_on) :
    U_t = (1 - ρ) * V_on / ((T : ℝ) * (N : ℝ)) → 0 ≤ U_t := by
  intro h_def
  -- We use A2 which already guarantees 0 ≤ U_t
  have h := A2_absence_emission_dette U_t V_on ρ T N h_rho h_params h_V
  -- A2 gives the form of U_t AND its positivity
  have h_eq : U_t = (1 - ρ) * V_on / ((T : ℝ) * (N : ℝ)) := h.left
  have h_pos : 0 ≤ U_t := h.right
  -- We ignore the redundancy: we keep only the positivity
  exact h_pos

/-! ## T6: Uniform distribution of UBI

  If we distribute U_total uniformly among N beneficiaries,
  each receives U_total / N.
-/
theorem T6_distribution_uniforme
    (U_total : ℝ) (N : ℕ) (h_N : 0 < N)
    (beneficiaires : List CompteUtilisateur)
    (h_card : beneficiaires.length = N) :
    let U_par_personne := U_total / (N : ℝ)
    let alloc := fun (_ : CompteUtilisateur) => U_par_personne
    (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
    (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_total := by
  intro U_par_personne alloc h_pos
  exact A12_distribution_RU U_total beneficiaires alloc h_pos

/-! # Section 5: SECURITY THEOREMS (T7-T8) -/

/-! ## T7: Impossibility of double-spending
  Source: Axiom A3 + A23

  If the sum of two transactions exceeds the available balance,
  the account cannot finance both simultaneously.
-/
theorem T7_pas_double_depense
    (cu : CompteUtilisateur)
    (tx1 tx2 : Transaction)
    (h_depassement : tx1.montant + tx2.montant > cu.wallet_V) :
    ¬ (ValidSig cu tx1 ∧ ValidSig cu tx2 ∧ cu.wallet_V ≥ tx1.montant + tx2.montant) := by
  intro h
  rcases h with ⟨h_sig1, h_sig2, h_cover⟩
  -- Contradiction between h_depassement (>) and h_cover (≥)
  have h_contra : tx1.montant + tx2.montant ≤ cu.wallet_V := by
    linarith [h_cover]
  -- The contradiction is now explicit
  linarith [h_depassement, h_contra]




/-! ## T8: Protection against enterprise bankruptcy
  Source: Axiom A21

  TAPs are guaranteed by the reserve.
-/
theorem T8_protection_TAP
    (ce : CompteEntrepriseEtendu) :
    let V_reserve := ce.tresorerie_V + (ce.NFT_financiers.map (·.valeur)).sum
    let TAP_total := (ce.TAP_en_cours.map (·.montant_avance)).sum
    TAP_total ≤ 0.8 * V_reserve := by
  intro V_reserve TAP_total
  -- A21 expresses exactly this bound
  simpa [V_reserve, TAP_total] using A21_capacite_TAP ce

/-! # Section 6: RESILIENCE THEOREMS (T9-T10) -/

/-! ## T9: Uniqueness of accounts (anti-Sybil)

  Two accounts with the same (TU, VC) pair are identical.
-/
theorem T9_unicite_comptes
    (cu1 cu2 : CompteUtilisateur)
    (h_tu : cu1.tu = cu2.tu)
    (h_vc : cu1.vc = cu2.vc) :
    cu1 = cu2 := by
  -- Directly A23
  have h := A23_anti_sybil cu1 cu2
  have h' : cu1.tu = cu2.tu ∧ cu1.vc = cu2.vc := ⟨h_tu, h_vc⟩
  exact h h'

/-! ## T10: Uniqueness of real assets

  Two assets with the same hash_unicite are identical.
-/
theorem T10_unicite_biens
    (bien1 bien2 : ActifReel)
    (h_hash : bien1.hash_unicite = bien2.hash_unicite) :
    bien1 = bien2 :=
  A14_unicite_biens bien1 bien2 h_hash

/-! # Section 7: CIRCULATION THEOREMS (T11-T13) -/

/-! ## T11: Bounded V→U conversion

  The V → U conversion is always positive and bounded by 2 * V.
-/
theorem T11_conversion_bornee
    (V_source kappa : ℝ)
    (h_V : 0 ≤ V_source)
    (h_kappa : 0.5 ≤ kappa ∧ kappa ≤ 2.0) :
    let U_obtenu := kappa * V_source
    0 ≤ U_obtenu ∧ U_obtenu ≤ 2.0 * V_source := by
  have h := A15_conversion_regulee V_source kappa h_V h_kappa
  constructor
  · exact h
  · nlinarith [h_kappa.2, h_V]

/-! ## T12: Stacking conserves energy
  Source: Axiom A17

  ΔV_avance = ΔD_stack (neutrality)
-/
theorem T12_stacking_conservatif
    (stack : Stacking) (D_stack : ℝ) :
    let V_avance := stack.montant_initial
    V_avance = D_stack := by
  intro V_avance
  -- Direct application of the stacking neutrality axiom
  exact A17_stacking_neutre stack D_stack

/-! ## T13: Total organic distribution

  The sum (part_collaborateurs + part_tresorerie) equals ΔV.
-/
theorem T13_distribution_totale
    (ce : CompteEntrepriseEtendu) (ΔV : ℝ) (h_pos : 0 < ΔV) :
    let part_collab := 0.4 * ΔV
    let part_treso := 0.6 * ΔV
    part_collab + part_treso = ΔV := by
  have := A22_distribution_organique ce ΔV h_pos
  simpa using this

/-! # Section 8: THERMODYNAMIC THEOREMS (T14-T16) -/

/-! ## T14: Explicit definition of the thermometer

  r_t = D_total / V_on_total
-/
theorem T14_thermometre_bien_defini (rad : RAD) :
    let r_t := thermometre rad
    r_t = rad.D_total / rad.V_on_total := by
  rfl

/-! ## T15: η remains in [0.5, 2.0]
  Source: RAD structure definition

  The η coefficient is always bounded by construction in the RAD structure.
  This replaces the previous proof using A20, which now only describes
  the adjustment dynamics.
-/
theorem T15_eta_borne (rad : RAD) :
    0.5 ≤ rad.eta ∧ rad.eta ≤ 2.0 := by
  -- Directly from h_eta field in RAD structure
  exact rad.h_eta

/-! ## T16: Forced circulation of treasury

  An enterprise's treasury cannot grow indefinitely:
  it is bounded by 1.2 × the average of 3 cycles.
-/
theorem T16_circulation_forcee
    (ce : CompteEntrepriseEtendu) (moyenne_3cycles : ℝ)
    (_h_positif : 0 ≤ moyenne_3cycles) :
    ce.tresorerie_V ≤ 1.2 * moyenne_3cycles := by
  exact A25_limite_retention ce moyenne_3cycles

/-! # Section 9: COMPOSITE THEOREMS (T17-T20) -/

/-! ## T17: Chain of guarantees

  We group three fundamental guarantees:
  - Validity of signatures (A3)
  - Complete distribution of UBI (A12)
  - Conservation of wealth (A27)
-/
theorem T17_chaine_garanties :
    (∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx) ∧
    (∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
        (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
          (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t) ∧
      (∀ (sys : SystemState), sys.V_total = sys.V_on + sys.V_immo) := by
  constructor
  · intro cu tx
    exact A3_inviolabilite_transactions cu tx
  constructor
  · intro U_t beneficiaires alloc h_pos
    exact A12_distribution_RU U_t beneficiaires alloc h_pos
  · intro sys
    exact A27_conservation_patrimoine sys

/-! ## T18: Backward compatibility

  The core theorems (closed contract, positivity of values)
  remain true in the extended system.
-/
theorem T18_compatibilite_ascendante :
    (∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx) ∧
    (∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D) := by
  constructor
  · intro cu tx
    exact A3_inviolabilite_transactions cu tx
  · intro v
    exact T_conservation_thermodynamique_valeurs v

/-! ## T19: Global coherence of quantities

  All components of Valeurs are positive or zero.
-/
theorem T19_coherence_globale (v : Valeurs) :
    0 ≤ v.S ∧ 0 ≤ v.U ∧ 0 ≤ v.V ∧ 0 ≤ v.D := by
  -- Directly from the definition of Valeurs
  exact ⟨v.hS, v.hU, v.hV, v.hD⟩

/-! ## T20: Complete productive NFT

  Every NFT with value has a Stipulat and a genealogy.
-/
theorem T20_nft_complet (nft : NFT) (h_valeur : 0 < nft.valeur) :
    0 < nft.stipulat ∧ (nft.genealogie ≠ [] ∨ nft.valeur = 0) := by
  constructor
  · -- Strictly positive Stipulat
    have h_cycle := A26_cycle_nft_productif nft
    exact (h_cycle.1) h_valeur
  · -- Non-empty genealogy (first case of the alternative)
    left
    have h_cycle := A26_cycle_nft_productif nft
    exact (h_cycle.2) h_valeur


