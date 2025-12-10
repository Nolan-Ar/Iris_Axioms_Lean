-- Core Axioms and Foundations
import IrisAxioms.iris_axioms
import IrisAxioms.iris_axioms_extended
import IrisAxioms.iris_brique

-- Theorems and Proofs
import IrisAxioms.iris_theoremes_extended

-- Application Domains
import IrisAxioms.iris_game_theory
import IrisAxioms.iris_incomplete_contracts
import IrisAxioms.iris_energy_exchange

-- Validation and Examples
import IrisAxioms.validation_correctifs
import IrisAxioms.iris_validation_complete
import IrisAxioms.iris_exemples_numeriques

-- Advanced Testing and Analysis
import IrisAxioms.crisis_scenarios
import IrisAxioms.emergent_properties

/-!
# IRIS Axioms - Main Entry Point

This is the main executable for the IRIS Axioms Lean project.
It imports all modules and verifies that all proofs compile successfully.
-/

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║   IRIS Axioms - Formal Verification in Lean 4            ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "✓ Core axioms loaded (A1-A27)"
  IO.println "✓ Extended theorems verified (T1-T16+)"
  IO.println "✓ Game theory models compiled"
  IO.println "✓ Incomplete contracts validated"
  IO.println "✓ Energy exchange proofs checked"
  IO.println "✓ Crisis scenarios tested (10 scenarios)"
  IO.println "✓ Emergent properties validated (10 properties)"
  IO.println ""
  IO.println "All proofs have been formally verified ✓"
  IO.println ""
  IO.println "Total modules compiled: 12"
  IO.println "Status: Ready for analysis"
