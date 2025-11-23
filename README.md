# IRIS Axioms - Formal Verification in Lean 4

Mathematical formalization of IRIS (Integrated Resource Information System) axioms in Lean 4, with verified proofs of consistency and economic properties.

## Description

This project formalizes an economic system based on:
- **Fundamental Axioms**: Monetary conservation, universal basic income distribution, inviolability
- **Game Theory**: Strategies, Nash equilibria, incentive mechanisms
- **Incomplete Contracts**: Partial validation, conflict resolution
- **Energy Exchange**: Modeling of energy flows
- **NFTs and Genealogy**: Cryptographic traceability

## Quick Start

### Prerequisites

- **Lean 4** (v4.24.0)
- **Git**
- **curl** (for elan)
- At least **4 GB of available RAM**
- **~10 GB of disk space** (for Mathlib and dependencies)

### Automatic Installation

```bash
# Clone the project
git clone https://github.com/Nolan-Ar/Iris_Axioms_Lean.git
cd Iris_Axioms_Lean

# Run the installation script
chmod +x setup.sh
./setup.sh
```

### Manual Installation

#### 1. Install elan (Lean version manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Then restart your terminal or run:
```bash
source ~/.profile  # or ~/.bashrc depending on your shell
```

#### 2. Verify Lean installation

```bash
lean --version  # Should display: Lean (version 4.24.0, ...)
lake --version  # Lake is Lean's build tool
```

#### 3. Fetch project dependencies

```bash
lake update
```

#### 4. Build the project

```bash
lake build
```

**Note**: The first build can take **20-40 minutes** as Mathlib (Lean's standard mathematical library) needs to be compiled.

## Usage

### Build the project

```bash
# Full build
lake build

# Or use the Makefile
make build
```

### Run the program

```bash
# Run the main executable
lake exe irisaxioms

# Or
make run
```

Displays: `IRIS compiled. All proofs have been verified`

### Verify proofs

```bash
# Verify a specific file
lean IrisAxioms/iris_axioms.lean

# Clean and rebuild
make clean
make build
```

### Working with VS Code

1. Install [VS Code](https://code.visualstudio.com/)
2. Install the **Lean 4** extension (ID: `leanprover.lean4`)
3. Open the project folder in VS Code
4. `.lean` files will benefit from:
   - Syntax highlighting
   - Real-time error messages
   - Autocompletion
   - Theorem tooltips

## Project Structure

```
Iris_Axioms_Lean/
├── IrisAxioms/
│   ├── iris_axioms.lean                 # Core IRIS axioms
│   ├── iris_axioms_extended.lean        # Extended axioms
│   ├── iris_theoremes_extended.lean     # Advanced theorems
│   ├── iris_brique.lean                 # Basic building blocks (TU, VC, Hash)
│   ├── iris_game_theory.lean            # Applied game theory
│   ├── iris_incomplete_contracts.lean   # Incomplete contracts
│   ├── iris_energy_exchange.lean        # Energy exchange
│   ├── iris_exemples_numeriques.lean    # Examples and practical cases
│   ├── iris_validation_complete.lean    # Global validation
│   └── validation_correctifs.lean       # Validation fixes
├── IrisAxioms.lean                      # Library entry point
├── Main.lean                            # Main program
├── lakefile.lean                        # Lake configuration (build)
├── lean-toolchain                       # Lean version (v4.24.0)
└── README.md                            # This file
```

## Main Modules

### 1. `iris_axioms.lean`
Defines the fundamental axioms:
- **Monetary Conservation**: S + U + V + D = 0
- **UBI Distribution**: Universal basic income mechanism
- **Inviolability**: Cryptographic protection via signatures

Main structures:
- `Valeurs`: Economic quantities (S, U, V, D)
- `CompteUtilisateur`: Wallets and CNP patrimony
- `NFT`: Non-fungible tokens with genealogy
- `Transaction`: Value transfers with proofs

### 2. `iris_game_theory.lean`
Models strategic interactions:
- Two-player games
- Nash equilibria
- Incentive mechanisms
- Equilibrium stability theorem

### 3. `iris_incomplete_contracts.lean`
Management of partially defined contracts:
- Partial specification of clauses
- Conflict resolution mechanisms
- Valid partial execution theorem

### 4. `iris_energy_exchange.lean`
Modeling of energy flows:
- Energy conservation
- Energy-money equivalence
- Transfer efficiency

## Usage Examples

### Create a transaction

```lean
import IrisAxioms.iris_axioms

open IrisAxioms

def example_transaction : Transaction := {
  emetteur := TU.mk "Alice"
  recepteur := TU.mk "Bob"
  montant_V := 100.0
  montant_U := 50.0
  preuve_signature := Hash.mk "cryptographic_signature"
  horodatage := 1234567890
  h_montant_V := by norm_num
  h_montant_U := by norm_num
}
```

### Verify monetary conservation

```lean
-- See IrisAxioms/iris_exemples_numeriques.lean
theorem conservation_example : ∃ v : Valeurs, v.S + v.U + v.V + v.D = 0 := by
  use { S := 1000, U := 500, V := -1200, D := -300,
        hS := by norm_num, hU := by norm_num,
        hV := by norm_num, hD := by norm_num }
  norm_num
```

## Useful Commands

```bash
# Quick build (without Mathlib)
lake build IrisAxioms

# Clean compiled files
lake clean

# Update dependencies
lake update

# Search for theorems
lake env lean --run search_tool.lean

# Format code
lake exe format
```

## Troubleshooting

### Error: `lake: command not found`

Make sure elan is properly installed and in your PATH:
```bash
source ~/.profile
elan toolchain list
```

### Error: Very slow compilation

This is normal for the first Mathlib compilation. To speed up:
```bash
# Download pre-compiled Mathlib binaries
lake exe cache get
```

### Error: `unknown package 'mathlib'`

```bash
lake update
lake clean
lake build
```

### Memory issues

Mathlib requires a lot of RAM. If compilation fails:
- Close other applications
- Increase system swap
- Compile module by module instead of `lake build`

## Lean Documentation

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) (community)

## Contributing

1. Fork the project
2. Create a branch (`git checkout -b feature/improvement`)
3. Commit your changes (`git commit -m 'Add new feature'`)
4. Push to the branch (`git push origin feature/improvement`)
5. Open a Pull Request

### Code Standards

- **Complete proofs**: No `sorry`
- **Documentation**: `/-! ... -/` comments for sections
- **Naming**: CamelCase for types, snake_case for definitions
- **Tests**: Numerical examples in `iris_exemples_numeriques.lean`

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

Copyright (c) 2025 Nolan-Ar

## Contact

For any questions or suggestions, open an issue on GitHub.

---

**Status**: All proofs are verified and complete (no `sorry`)

**Lean Version**: 4.24.0
**Mathlib Version**: 4.24.0
