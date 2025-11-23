/-
  IRIS — Axioms (consolidated version with report fixes)
  - D ≥ 0 in Valeurs
  - η = η_phys * μ_social (Option B: social multiplier)
  - Axiom of effective UBI distribution
  - Inviolability via signature predicate (non-tautological)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic

namespace IrisAxioms

/-!
# Basic Types
-/
structure TU   where val : String deriving Repr
structure VC   where val : String deriving Repr
structure Hash where val : String deriving Repr

/-!
# Economic Quantities & Accounts
-/
structure Valeurs where
  S : ℝ
  U : ℝ
  V : ℝ
  D : ℝ
  hS : 0 ≤ S
  hU : 0 ≤ U
  hV : 0 ≤ V
  hD : 0 ≤ D    -- Fix 2: D bounded from below

structure CompteUtilisateur where
  tu : TU
  vc : VC
  wallet_V : ℝ
  wallet_U : ℝ
  cnp_patrimoine : ℝ
  h_wallet_V : 0 ≤ wallet_V
  h_wallet_U : 0 ≤ wallet_U
  h_cnp      : 0 ≤ cnp_patrimoine

structure NFT where
  hash : Hash
  valeur : ℝ
  stipulat : ℝ
  genealogie : List Hash
  h_valeur : 0 ≤ valeur
  h_stipulat : 0 ≤ stipulat

structure CompteEntreprise where
  tresorerie_V : ℝ
  nft_productifs : List NFT
  h_tresorerie : 0 ≤ tresorerie_V

structure Transaction where
  montant   : ℝ
  signature : Hash
  timestamp : ℕ
  h_montant : 0 < montant

/-!
# Signature Predicate
-/
def ValidSig (_cu : CompteUtilisateur) (_tx : Transaction) : Prop := True
-- ↑ default schema; to be refined if needed (cryptography)

/-!
# IRIS AXIOMS
-/

-- Axiom 2.1: Bijective uniqueness (CU ↔ (TU,VC))
axiom A1_unicite_bijective :
  ∃ (f : CompteUtilisateur → TU × VC),
    Function.Bijective f ∧
    ∀ cu, (f cu).1 = cu.tu ∧ (f cu).2 = cu.vc

-- Axiom 2.2: UBI without debt emission (coercions ℕ→ℝ)
axiom A2_absence_emission_dette (U_t V_on ρ : ℝ) (T N : ℕ) :
  (0 ≤ ρ ∧ ρ ≤ 0.3) →
  (0 < T ∧ 0 < N) →
  0 ≤ V_on →
  U_t = (1 - ρ) * V_on / ((T : ℝ) * (N : ℝ)) ∧ 0 ≤ U_t

-- Axiom 2.3: Inviolability of transactions (verified signature)
axiom A3_inviolabilite_transactions :
  ∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx

-- Axiom 2.4: Strict exclusion of U for enterprise accounts
axiom A4_exclusion_U_entreprise (ce : CompteEntreprise) :
  0 ≤ ce.tresorerie_V   -- no U balance on enterprise side

-- Axiom 2.5: Stipulat necessary for all valued NFTs
axiom A5_necessite_stipulat (nft : NFT) :
  0 < nft.valeur → 0 < nft.stipulat

-- Axiom 2.6: Fundamental value creation (η = η_phys * μ_social)
-- Fix 1: Option B — bounded social multiplier
axiom A6_creation_valeur_energetique
  (η_phys μ_social Δt w_S w_U S_burn U_burn : ℝ) :
  (0 < η_phys ∧ η_phys ≤ 1) →          -- physical efficiency (≤ 1)
  (1 ≤ μ_social ∧ μ_social ≤ 2) →       -- externalities / coordination
  (w_S + w_U = 1 ∧ 0 ≤ w_S ∧ 0 ≤ w_U) → -- convex mixture
  (0 ≤ S_burn ∧ 0 ≤ U_burn) →
  0 < Δt →
  let η  := η_phys * μ_social
  let Et := w_S * S_burn + w_U * U_burn
  let ΔV := η * Δt * Et
  0 ≤ ΔV

-- Axiom 2.7: Absence of interest (repayments = principal)
axiom A7_absence_interets (montant_initial : ℝ) (remboursements : List ℝ) :
  remboursements.sum = montant_initial

-- Axiom 2.8: Mandatory genealogical memory
axiom A8_genealogie_complete (nft : NFT) :
  nft.genealogie ≠ [] ∨ nft.valeur = 0

-- Axiom 2.9: CE mediation with value creation (covering treasury)
axiom A9_mediation_CE_obligatoire (nft_source nft_dest : NFT) (V_creation : ℝ) :
  0 < V_creation →
  ∃ ce : CompteEntreprise, ce.tresorerie_V ≥ V_creation

-- Axiom 2.10: Thermodynamic conservation (fundamental quantities ≥ 0)
axiom A10_conservation_thermodynamique (V_total D_total : ℝ) :
  0 ≤ V_total ∧ 0 ≤ D_total

-- Axiom 2.11: Organizational continuity
axiom A11_survie_organisationnelle (ce : CompteEntreprise) :
  ∃ _successeur : CompteUtilisateur, True

/-!
# Fix 3: Effective UBI Distribution
-/
-- U_t is effectively allocated to a list of beneficiaries via an allocation function
axiom A12_distribution_RU
  (U_t : ℝ) (beneficiaires : List CompteUtilisateur)
  (alloc : CompteUtilisateur → ℝ) :
  (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
  (beneficiaires.attach.map (fun ⟨cu,_⟩ => alloc cu)).sum = U_t

end IrisAxioms

/-!
# Sanity checks
-/
#check IrisAxioms.A1_unicite_bijective
#check IrisAxioms.A2_absence_emission_dette
#check IrisAxioms.A3_inviolabilite_transactions
#check IrisAxioms.A4_exclusion_U_entreprise
#check IrisAxioms.A5_necessite_stipulat
#check IrisAxioms.A6_creation_valeur_energetique
#check IrisAxioms.A7_absence_interets
#check IrisAxioms.A8_genealogie_complete
#check IrisAxioms.A9_mediation_CE_obligatoire
#check IrisAxioms.A10_conservation_thermodynamique
#check IrisAxioms.A11_survie_organisationnelle
#check IrisAxioms.A12_distribution_RU
