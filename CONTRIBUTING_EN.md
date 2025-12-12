# Contributing to IRIS Axioms

Thank you for your interest in contributing to the IRIS Axioms project! This document provides guidelines and best practices for contributing.

## Table of Contents

1. [Getting Started](#getting-started)
2. [Development Workflow](#development-workflow)
3. [Code Standards](#code-standards)
4. [Proof Guidelines](#proof-guidelines)
5. [Documentation](#documentation)
6. [Testing](#testing)
7. [Pull Request Process](#pull-request-process)

## Getting Started

### Prerequisites

Before contributing, make sure you have:
- Lean 4 (v4.24.0) installed via elan
- Git configured on your machine
- VS Code with the Lean 4 extension (recommended)
- Basic understanding of Lean 4 syntax and theorem proving

### Setting Up Your Development Environment

1. Fork the repository on GitHub
2. Clone your fork locally:
   ```bash
   git clone https://github.com/YOUR_USERNAME/Iris_Axioms_Lean.git
   cd Iris_Axioms_Lean
   ```
3. Add the upstream repository:
   ```bash
   git remote add upstream https://github.com/Nolan-Ar/Iris_Axioms_Lean.git
   ```
4. Install dependencies:
   ```bash
   lake update
   lake build
   ```

## Development Workflow

### Creating a New Feature or Fix

1. **Sync with upstream**:
   ```bash
   git fetch upstream
   git checkout main
   git merge upstream/main
   ```

2. **Create a feature branch**:
   ```bash
   git checkout -b feature/your-feature-name
   ```
   Use descriptive branch names:
   - `feature/add-xyz` for new features
   - `fix/bug-description` for bug fixes
   - `docs/what-you-document` for documentation
   - `refactor/what-you-refactor` for refactoring

3. **Make your changes** following the code standards below

4. **Verify your changes**:
   ```bash
   lake build
   ```

5. **Commit your changes**:
   ```bash
   git add .
   git commit -m "Brief description of changes"
   ```

## Code Standards

### Naming Conventions

- **Types and Structures**: Use `CamelCase`
  ```lean
  structure CompteUtilisateur where
  structure NFT where
  ```

- **Definitions and Theorems**: Use `snake_case`
  ```lean
  def calculate_total : ℝ → ℝ := ...
  theorem conservation_monetaire : ...
  ```

- **Axioms**: Prefix with `A` followed by number
  ```lean
  axiom A1_unicite_bijective : ...
  axiom A2_absence_emission_dette : ...
  ```

### Code Structure

1. **Imports**: Group imports logically
   ```lean
   import Mathlib.Data.Real.Basic
   import Mathlib.Tactic
   import IrisAxioms.iris_axioms
   ```

2. **Namespace**: Use appropriate namespaces
   ```lean
   namespace IrisAxioms
   -- Your code here
   end IrisAxioms
   ```

3. **Sections**: Use documentation comments to organize code
   ```lean
   /-!
   # Section Title
   Brief description of what this section contains
   -/
   ```

### Code Quality

- **No `sorry`**: All proofs must be complete
- **Type Safety**: Leverage Lean's type system
- **Invariants**: Use structure fields to encode invariants
  ```lean
  structure Valeurs where
    S : ℝ
    hS : 0 ≤ S  -- Invariant: S is non-negative
  ```

## Proof Guidelines

### Writing Proofs

1. **Clarity over Brevity**: Prefer readable proofs
   ```lean
   -- Good: Clear steps
   theorem example : P → Q := by
     intro h
     apply some_lemma
     exact h

   -- Acceptable for simple cases
   theorem example : P → Q := some_lemma
   ```

2. **Use Appropriate Tactics**:
   - `norm_num` for numerical reasoning
   - `simp` for simplification
   - `omega` for linear arithmetic
   - `constructor` for building structures
   - `cases` for pattern matching

3. **Comment Complex Proofs**:
   ```lean
   theorem complex_result : ... := by
     -- Step 1: Establish the base case
     have h1 : ... := ...
     -- Step 2: Use induction on n
     induction n with
     | zero => ...
     | succ n ih => ...
   ```

### Proof Style

- Break long proofs into lemmas
- Name intermediate results descriptively
- Use `have` for intermediate steps
- Use `calc` for equational reasoning:
  ```lean
  calc
    a = b := by ...
    _ = c := by ...
    _ = d := by ...
  ```

## Documentation

### Code Comments

1. **Module-Level Documentation**:
   ```lean
   /-
   Module: iris_axioms.lean
   Description: Core IRIS axioms and fundamental structures
   Author: [Your Name]
   Date: YYYY-MM-DD
   -/
   ```

2. **Section Comments**:
   ```lean
   /-!
   # Monetary Conservation
   This section defines the monetary conservation axiom and related theorems.
   -/
   ```

3. **Function/Theorem Documentation**:
   ```lean
   /--
   Computes the universal basic income for a given period.

   - `V_on`: Total value created
   - `rho`: Reserve ratio (0 ≤ ρ ≤ 0.3)
   - `T`: Number of periods
   - `N`: Number of beneficiaries
   -/
   def compute_UBI (V_on : ℝ) (rho : ℝ) (T N : ℕ) : ℝ := ...
   ```

### Documentation Language

- **Documentation can be in English or French** (bilingual project)
- User-facing documentation (README, CONCEPTS) should be available in both languages
- Code comments and internal documentation are preferably in English
- Use clear, concise language
- Provide examples when helpful
- Explain economic concepts for non-experts

## Testing

### Adding Examples

Add numerical examples to `iris_exemples_numeriques.lean`:

```lean
/-- Example: Simple transaction validation -/
def example_simple_transaction : Transaction := {
  montant := 100.0
  signature := Hash.mk "example_sig"
  timestamp := 1234567890
  h_montant := by norm_num
}

/-- Verify the transaction is valid -/
theorem example_transaction_valid :
    0 < example_simple_transaction.montant := by
  norm_num
```

### Verification Checklist

Before submitting:
- [ ] All files compile without errors: `lake build`
- [ ] No `sorry` in proofs
- [ ] Added tests/examples for new features
- [ ] Documentation is complete and in English
- [ ] Code follows naming conventions

## Pull Request Process

### Before Submitting

1. **Update from upstream**:
   ```bash
   git fetch upstream
   git rebase upstream/main
   ```

2. **Run full build**:
   ```bash
   lake clean
   lake build
   ```

3. **Review your changes**:
   ```bash
   git diff main
   ```

### Submitting a Pull Request

1. Push your branch to your fork:
   ```bash
   git push origin feature/your-feature-name
   ```

2. Go to GitHub and create a Pull Request

3. **PR Title**: Use descriptive titles
   - `Add: Description` for new features
   - `Fix: Description` for bug fixes
   - `Docs: Description` for documentation
   - `Refactor: Description` for refactoring

4. **PR Description**: Include:
   - What changes were made
   - Why the changes were necessary
   - Any relevant issue numbers
   - Testing performed

### PR Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] New feature
- [ ] Bug fix
- [ ] Documentation
- [ ] Refactoring

## Changes Made
- List of specific changes
- With details

## Testing
- Describe testing performed
- Include example usage if applicable

## Checklist
- [ ] Code compiles without errors
- [ ] No `sorry` in proofs
- [ ] Documentation updated
- [ ] Examples added (if applicable)
- [ ] Follows code standards
```

### Code Review

- Be open to feedback and suggestions
- Respond to review comments promptly
- Make requested changes in new commits
- Once approved, maintainers will merge your PR

## Best Practices

### Performance

- Avoid computationally expensive tactics in large proofs
- Use `#check` to verify types before complex proofs
- Cache intermediate results with `let` or `have`

### Maintainability

- Keep functions and proofs focused and single-purpose
- Extract common patterns into lemmas
- Maintain consistent style throughout the file

### Collaboration

- Communicate in issues before starting major changes
- Ask questions in discussions or issues
- Help review others' PRs when possible

## Resources

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

## Questions?

If you have questions:
1. Check existing issues and discussions
2. Ask in GitHub Discussions
3. Open a new issue with the `question` label

Thank you for contributing to IRIS Axioms!
