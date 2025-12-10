# IRIS CONCEPTS - Mathematical and Economic Lexicon

This document explains in detail the economic concepts of the IRIS system and their mathematical formalization in Lean 4.

## Table of Contents

- [Thermodynamic Concepts](#thermodynamic-concepts)
- [Transformation Coefficients](#transformation-coefficients)
- [Automatic Regulation](#automatic-regulation)
- [Economic Mechanisms](#economic-mechanisms)
- [Concrete Examples](#concrete-examples)
- [Mathematical Properties](#mathematical-properties)

## Thermodynamic Concepts

IRIS models the economy as a thermodynamic system where energy (work, money) is conserved and transformed.

### The Four Fundamental Quantities

| IRIS Term | Lean Structure | Constraint | Economic Meaning |
|-----------|----------------|------------|------------------|
| **Verum (V)** | `Valeurs.V : ℝ` | `V ≥ 0` | **Living value**: Productive assets in circulation |
| **Debt (D)** | `Valeurs.D : ℝ` | `D ≤ 0` | **Thermodynamic commitment**: Debt created during production |
| **Stipulat (S)** | `Valeurs.S : ℝ` | `S ≥ 0` | **Proof of effort**: Energy expended, work accomplished |
| **Unum (U)** | `Valeurs.U : ℝ` | `U ≥ 0` | **Usage currency**: Perishable medium of exchange |

### Thermodynamic Conservation (Axiom A1)

```lean
axiom A1_conservation : ∀ (v : Valeurs), v.S + v.U + v.V + v.D = 0
```

**Interpretation**:
- The algebraic sum of the four quantities is always zero
- Any value creation (V > 0) generates equal debt (D < 0)
- Energy expended (S) and payments (U) exactly compensate
- **Physical analogy**: First law of thermodynamics (energy conservation)

### Decomposition of V (Axiom A2)

```lean
axiom A2_decomposition_V : ∀ (sys : SystemState),
  sys.V_total = sys.V_on + sys.V_immo
```

- **V_on**: Value "in the money" (active and liquid)
- **V_immo**: Immobilized value (patrimony, CNP)

**Example**:
- Alice has €1,000 in the bank (V_on) + a house worth €200,000 (V_immo)
- V_total = 1,000 + 200,000 = €201,000

## Transformation Coefficients

### η - Value Creation Coefficient (Axiom A18)

```lean
structure CoefficientsCreation where
  eta : ℝ
  psi : ℝ
  h_eta : 0 < eta ∧ eta ≤ 2
  h_psi : 0 < psi ∧ psi ≤ 1
```

**Creation formula**:
```
ΔV = η × ψ × E
```

Where:
- **ΔV**: Value variation created
- **η**: Energy → value transformation efficiency
- **ψ**: Quality factor (0 < ψ ≤ 1)
- **E**: Energy expended (time × money)

### Decomposition of η

```
η = η_phys × μ_social
```

| Component | Range | Meaning |
|-----------|-------|---------|
| **η_phys** | (0, 1] | **Physical efficiency**: Technical process yield |
| **μ_social** | [1, 2] | **Social multiplier**: Social impact of activity |

**Examples**:
1. **Polluting industry**: η_phys = 0.9 (very efficient), μ_social = 1.0 (neutral impact) → η = 0.9
2. **Public school**: η_phys = 0.6 (high cost), μ_social = 1.8 (strong social impact) → η = 1.08
3. **Tech startup**: η_phys = 0.8, μ_social = 1.5 → η = 1.2

### κ - Conversion Coefficient U → V (Axiom A5)

```lean
axiom A5_conversion_U_V : ∀ (cu : CompteUtilisateur) (montant_U : ℝ),
  0 ≤ montant_U →
  ∃ (kappa : ℝ), 0 < kappa ∧ kappa ≤ 1 ∧
  (cu with wallet_V := cu.wallet_V + kappa * montant_U,
           wallet_U := cu.wallet_U - montant_U).wallet_V ≥ 0
```

**Interpretation**:
- κ represents the U → V exchange rate
- 1 Unum (U) converted gives κ Verum (V)
- κ ≤ 1 because U is perishable (value loss)
- **Example**: With κ = 0.95, converting 100U gives 95V

### ρ - UBI Retention Rate (Axiom A13)

```lean
axiom A13_perissabilite_U : ∀ (U_t : ℝ) (rho : ℝ),
  0 ≤ rho ∧ rho < 1 →
  let U_next := (1 - rho) * U_t
  U_next < U_t
```

**U Expiration**:
- Each cycle, a fraction ρ of U disappears
- Encourages rapid circulation
- **Example**: With ρ = 0.05 (5% per month), 100U becomes 95U after one month

## Automatic Regulation

### Economic Thermometer (Axiom A19)

```lean
def thermometre (rad : RAD) : ℝ := rad.D_total / rad.V_on_total
```

**Temperature Zones**:

```
r_t = D_total / V_on_total

┌─────────────────────────────────────────────────────┐
│  r_t < 0.85         │  "COLD"      │  Deflation     │
│  ────────────────────────────────────────────────── │
│  0.85 ≤ r_t ≤ 1.15  │  EQUILIBRIUM │  Stable        │
│  ────────────────────────────────────────────────── │
│  r_t > 1.15         │  "HOT"       │  Inflation     │
└─────────────────────────────────────────────────────┘
```

**Interpretation**:
- **r_t < 0.85**: Too much value (V) relative to debt (D) → Deflation → Increase η
- **0.85 ≤ r_t ≤ 1.15**: Healthy equilibrium
- **r_t > 1.15**: Too much debt (D) relative to V → Inflation → Reduce η

### Automatic Adjustment of η (Axiom A20)

```lean
axiom A20_ajustement_eta : ∀ (rad_before rad_after : RAD),
  let r_t := thermometre rad_before
  (r_t > 1.15 → rad_after.eta < rad_before.eta) ∧
  (r_t < 0.85 → rad_after.eta > rad_before.eta) ∧
  (0.85 ≤ r_t ∧ r_t ≤ 1.15 → rad_after.eta = rad_before.eta)
```

**Feedback Mechanism**:
1. Measure r_t each cycle
2. If r_t > 1.15 (overheating): Reduce η by 5-10% → Less value creation
3. If r_t < 0.85 (cooling): Increase η by 5-10% → More creation
4. Otherwise: Keep η stable

**Numerical Example**:
```lean
-- Initial state: overheating
let rad_before : RAD := {
  D_total := 150000,
  V_on_total := 100000,  -- r_t = 1.5 > 1.15
  eta := 1.2,
  ...
}

-- Automatic adjustment: η ↓
let rad_after : RAD := {
  D_total := 150000,
  V_on_total := 100000,
  eta := 1.08,  -- Reduced by 10%
  ...
}
```

## Economic Mechanisms

### Universal Basic Income Distribution (Axiom A12)

```lean
axiom A12_distribution_RU :
  ∀ (beneficiaires : List CompteUtilisateur)
    (allocation : CompteUtilisateur → ℝ)
    (U_t : ℝ),
  0 ≤ U_t →
  (beneficiaires.attach.map (fun ⟨cu, _⟩ => allocation cu)).sum = U_t
```

**Operation**:
1. Each cycle, an amount U_t is distributed
2. Each beneficiary receives an allocation
3. Sum of allocations = U_t exactly (conservation)

**Calculation Formula**:
```
U_t = (1 - ρ) × V_on_total / (12 × 1000)
```

Where:
- ρ: Retention rate (e.g., 0.05)
- V_on_total: Total circulating value
- Division by 12: Monthly distribution
- Division by 1000: Normalization

**Example**:
- V_on_total = €1,000,000
- ρ = 0.05
- U_t = (1 - 0.05) × 1,000,000 / (12 × 1000) = €79.17 per month per person

### TAP - Treasury Advance Payroll (Axiom A21)

```lean
axiom A21_capacite_TAP : ∀ (ce : CompteEntrepriseEtendu),
  let reserve := ce.tresorerie_V + (ce.NFT_financiers.map (·.valeur)).sum
  let tap_total := (ce.TAP_en_cours.map (·.montant_avance)).sum
  tap_total ≤ 0.8 * reserve
```

**Prudential Rule**:
- A company can advance up to 80% of its reserves
- Reserves = V treasury + financial NFTs
- Limits leverage effect
- Prevents cascading bankruptcy

**Example**:
```lean
-- Company with reserves
let entreprise : CompteEntrepriseEtendu := {
  tresorerie_V := 50000,
  NFT_financiers := [nft1, nft2],  -- Total value: 30000
  TAP_en_cours := [tap1, tap2],     -- Total amount: 60000
  ...
}

-- Verification
reserve = 50000 + 30000 = 80000
tap_total = 60000
60000 ≤ 0.8 × 80000 = 64000  ✓ Valid
```

### Cryptographic Inviolability (Axiom A7)

```lean
axiom A7_pas_double_depense : ∀ (cu : CompteUtilisateur) (tx1 tx2 : Transaction),
  ValidSig cu tx1 → ValidSig cu tx2 →
  cu.wallet_V ≥ tx1.montant_V + tx2.montant_V
```

**Double-Spend Protection**:
- Two valid signed transactions cannot exceed the balance
- Guarantees system integrity
- Bitcoin analogy: prevents spending the same money twice

## Concrete Examples

### Example 1: Alice Creates Value

**Context**:
- Alice is a freelance developer
- She works 48 hours on a project
- Client pays 80 Unum
- Efficiency: η_phys = 0.8, μ_social = 1.5 → η = 1.2
- Quality: ψ = 1.0 (excellent work)

**Energy Calculation**:
```
E = α × time + β × money
E = 0.6 × 48 + 0.4 × 80
E = 28.8 + 32
E = 60.8
```

**Value Creation**:
```
ΔV = η × ψ × E
ΔV = 1.2 × 1.0 × 60.8
ΔV = 72.96 ≈ 73 Verum
```

**In Lean**:
```lean
example : let η := (0.8 : ℝ) * 1.5 in
          let ψ := (1.0 : ℝ) in
          let E := 0.6 * 48 + 0.4 * 80 in
          let ΔV := η * ψ * E in
          ΔV = 72.96 := by
  norm_num
```

### Example 2: System in Disequilibrium

**Crisis Scenario**:
```lean
-- Initial state: Economic overheating
let rad_crise : RAD := {
  D_total := 300000,     -- High debt
  V_on_total := 100000,  -- Low value
  eta := 2.0,            -- Creation too high
  kappa := 0.8,
  ...
}

-- Thermometer calculation
r_t = 300000 / 100000 = 3.0

-- Diagnosis: r_t = 3.0 > 1.15 → OVERHEATING
```

**Automatic Reaction** (A20):
1. Detection: r_t > 1.15
2. Action: Reduce η by 20%
3. New η: 2.0 × 0.8 = 1.6

```lean
theorem ajustement_crise : ∀ (rad_before rad_after : RAD),
  thermometre rad_before = 3.0 →
  A20_ajustement_eta rad_before rad_after →
  rad_after.eta < rad_before.eta := by
  intro rad_before rad_after h_thermo h_ajust
  have h_surchauffe : thermometre rad_before > 1.15 := by
    rw [h_thermo]
    norm_num
  exact (h_ajust.1 h_surchauffe)
```

### Example 3: Incomplete Contract

**Use Case**: Delivery contract with missing clauses

```lean
-- Possible states
inductive Outcome
| delivered_on_time
| delivered_late
| not_delivered

-- Incomplete contract
def contrat_livraison : PartialContract Outcome := fun ω =>
  match ω with
  | "on_time" => some delivered_on_time
  | "late" => some delivered_late
  | _ => none  -- Not specified (strike, disaster, etc.)

-- Contract refinement
def contrat_complete : PartialContract Outcome := fun ω =>
  match ω with
  | "on_time" => some delivered_on_time
  | "late" => some delivered_late
  | "strike" => some not_delivered  -- Added clause
  | _ => some not_delivered         -- Default fallback
```

**Theorem**: Refinement preserves existing commitments
```lean
theorem raffinement_preserving :
  refines_contract contrat_livraison contrat_complete := by
  intro ω h_spec
  cases ω with
  | "on_time" => simp [contrat_livraison, contrat_complete]
  | "late" => simp [contrat_livraison, contrat_complete]
```

## Mathematical Properties

### Quantity Positivity

```lean
-- V is always positive or zero
theorem V_non_negative : ∀ (v : Valeurs), 0 ≤ v.V := v.hV

-- S (work) is positive
theorem S_positive : ∀ (v : Valeurs), 0 ≤ v.S := v.hS

-- U (currency) is positive
theorem U_positive : ∀ (v : Valeurs), 0 ≤ v.U := v.hU

-- D (debt) is negative or zero
theorem D_non_positive : ∀ (v : Valeurs), v.D ≤ 0 := v.hD
```

### Coefficient Bounds

```lean
-- η is bounded
theorem eta_bounds : ∀ (coef : CoefficientsCreation),
  0 < coef.eta ∧ coef.eta ≤ 2 := coef.h_eta

-- κ is in (0, 1]
theorem kappa_bounds : ∀ (rad : RAD),
  0 < rad.kappa ∧ rad.kappa ≤ 1 := rad.h_kappa

-- μ_social in [1, 2]
theorem mu_social_bounds : ∀ (μ : ℝ),
  is_valid_mu_social μ → 1 ≤ μ ∧ μ ≤ 2 := by
  intro μ h
  exact h
```

### Conservation and Stability

```lean
-- Total conservation
theorem conservation_totale : ∀ (sys : SystemState),
  sys.V_total + sys.D_total + sys.S_total + sys.U_total = 0 := by
  intro sys
  exact sys.h_conservation

-- Thermometer stability
theorem thermometre_stable : ∀ (rad : RAD),
  let r_t := thermometre rad
  0.85 ≤ r_t ∧ r_t ≤ 1.15 →
  ∀ (rad' : RAD), A20_ajustement_eta rad rad' →
  rad'.eta = rad.eta := by
  intro rad r_t h_equilibre rad' h_ajust
  exact (h_ajust.2.2 h_equilibre)
```

## Comparison with Other Systems

| Concept | Traditional System | IRIS System |
|---------|-------------------|-------------|
| **Currency** | Single (Euro, Dollar) | Dual (U perishable, V durable) |
| **Creation** | Bank loan with interest | Work + energy → value |
| **Inflation** | Control by policy rates | Auto-regulation by thermometer |
| **Distribution** | Wages + benefits | Universal Basic Income (UBI) integrated |
| **Debt** | Infinite growth possible | Bounded by thermometer |
| **Guarantees** | Physical collateral | Cryptographic signatures |

## Technical Glossary

- **RAD**: Automatic Distribution Register
- **CNP**: Nominal Patrimonial Account (immobilized patrimony)
- **TAP**: Treasury Advance Payroll (salary advance)
- **NFT**: Non-Fungible Token (unique token with genealogy)
- **UBI**: Universal Basic Income
- **TU**: User Holder (unique identifier)
- **VC**: Cryptographic Verification (public key)

## References

For more depth, see:
- [REFERENCES.bib](REFERENCES.bib) - Complete bibliography
- [README.md](README.md) or [README_EN.md](README_EN.md) - General documentation
- [IrisAxioms/iris_axioms.lean](IrisAxioms/iris_axioms.lean) - Formal axioms

---

**Version**: 1.0
**Last Updated**: 2025-12-10
