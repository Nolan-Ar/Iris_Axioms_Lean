import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import IrisAxioms.iris_axioms_extended

namespace IrisEnergyExchange

open IrisAxiomsExtended

/-- Explicit definition of the value created during an energy exchange,
    in the spirit of axiom A6. -/
def deltaV (η_phys μ_social Δt w_S w_U S_burn U_burn : ℝ) : ℝ :=
  let η := η_phys * μ_social
  let Et := w_S * S_burn + w_U * U_burn
  η * Δt * Et

/-- Functional form of A6: under its hypotheses,
    the created value is always ≥ 0. -/
theorem deltaV_nonneg_from_axiom
    (η_phys μ_social Δt w_S w_U S_burn U_burn : ℝ)
    (h_phys : 0 < η_phys ∧ η_phys ≤ 1)
    (h_social : 1 ≤ μ_social ∧ μ_social ≤ 2)
    (h_convexe : w_S + w_U = 1 ∧ 0 ≤ w_S ∧ 0 ≤ w_U)
    (h_burn : 0 ≤ S_burn ∧ 0 ≤ U_burn)
    (h_dt : 0 < Δt) :
    0 ≤ deltaV η_phys μ_social Δt w_S w_U S_burn U_burn := by
  have h := A6_creation_valeur_energetique
    η_phys μ_social Δt w_S w_U S_burn U_burn
    h_phys h_social h_convexe h_burn h_dt
  simpa [deltaV] using h

/--
Energy exchange monotonicity theorem:

With fixed coefficients (η_phys, μ_social, Δt, w_S, w_U) satisfying A6,
if we increase both S_burn and U_burn, the created value ΔV
cannot decrease.
-/
theorem deltaV_mono
    (η_phys μ_social Δt w_S w_U S₁ S₂ U₁ U₂ : ℝ)
    (h_phys : 0 < η_phys ∧ η_phys ≤ 1)
    (h_social : 1 ≤ μ_social ∧ μ_social ≤ 2)
    (h_convexe : w_S + w_U = 1 ∧ 0 ≤ w_S ∧ 0 ≤ w_U)
    (h_dt : 0 < Δt)
    (hS : S₁ ≤ S₂)
    (hU : U₁ ≤ U₂) :
    deltaV η_phys μ_social Δt w_S w_U S₁ U₁
      ≤ deltaV η_phys μ_social Δt w_S w_U S₂ U₂ := by
  have h_wS_nonneg : 0 ≤ w_S := h_convexe.2.1
  have h_wU_nonneg : 0 ≤ w_U := h_convexe.2.2
  -- comparison of energies Et₁ and Et₂
  have hE :
      w_S * S₁ + w_U * U₁ ≤ w_S * S₂ + w_U * U₂ := by
    have h1 := mul_le_mul_of_nonneg_left hS h_wS_nonneg
    have h2 := mul_le_mul_of_nonneg_left hU h_wU_nonneg
    linarith
  -- non-negative multiplicative factor
  have hη_nonneg : 0 ≤ η_phys := le_of_lt h_phys.1
  have hμ_nonneg : 0 ≤ μ_social := by
    have : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans this h_social.1
  have hΔt_nonneg : 0 ≤ Δt := le_of_lt h_dt
  have h_factor_nonneg : 0 ≤ η_phys * μ_social * Δt := by
    have hημ_nonneg := mul_nonneg hη_nonneg hμ_nonneg
    exact mul_nonneg hημ_nonneg hΔt_nonneg
  -- multiply the inequality on Et by this factor
  have := mul_le_mul_of_nonneg_left hE h_factor_nonneg
  -- rewrite in terms of deltaV
  simpa [deltaV, mul_left_comm, mul_assoc, mul_comm] using this

/--
Additivity of value creation:

Two successive exchanges with the same coefficients are equivalent,
from an energetic perspective, to a single exchange for the sum
of burned Stipulats and U. -/
theorem deltaV_additive
    (η_phys μ_social Δt w_S w_U S₁ S₂ U₁ U₂ : ℝ) :
    deltaV η_phys μ_social Δt w_S w_U (S₁ + S₂) (U₁ + U₂)
      = deltaV η_phys μ_social Δt w_S w_U S₁ U₁
        + deltaV η_phys μ_social Δt w_S w_U S₂ U₂ := by
  -- purely algebraic proof
  simp [deltaV, add_left_comm, add_assoc, mul_add, mul_assoc]

end IrisEnergyExchange
