# Yang-Mills Mass Gap Research Project

This directory contains work related to the Yang-Mills Mass Gap Problem, one of the seven Millennium Prize Problems worth $1,000,000.

## Project Structure

```
DavidsMath/
├── code/
│   ├── simulations/     # Lattice gauge theory simulations
│   ├── visualization/   # Plotting and visualization tools
│   └── tests/          # Unit tests and verification
│       └── test_su2_gauge_group.py  # SU(2) property verification
│
├── notes/
│   ├── differential_geometry/  # Manifolds, Lie groups, bundles
│   ├── functional_analysis/    # Hilbert spaces, operators, spectra
│   ├── qft/                   # Quantum field theory
│   ├── lattice_theory/        # Lattice approximations
│   └── study_plan/            # Learning roadmap
│
├── proofs/
│   └── attempts/              # Proof attempts and strategies
│
├── DavidsMath/                # Lean 4 formalizations
│   ├── YangMillsMinimal.lean  # ✓ Builds successfully
│   ├── YangMillsTestStrategy.lean  # ✓ Builds successfully
│   └── YangMillsPrerequisites.lean  # Full formalization (complex)
│
└── tex/                       # LaTeX documentation
    ├── yangMillsMathematicalPrerequisites.tex
    └── yangMillsTestSetupStrategy.tex
```

## Quick Start

### 1. Test SU(2) Gauge Group Properties

```bash
cd code/tests
python test_su2_gauge_group.py
```

This verifies:
- Pauli matrices are Hermitian
- Lie algebra commutation relations [σᵢ, σⱼ] = 2iεᵢⱼₖσₖ
- Group elements are unitary with det = 1
- Closure under multiplication

### 2. Build Lean Formalizations

```bash
cd /home/david/Research/Math/DavidsMath
lake build DavidsMath.YangMillsMinimal
lake build DavidsMath.YangMillsTestStrategy
```

### 3. Compile LaTeX Documentation

```bash
cd tex
pdflatex yangMillsMathematicalPrerequisites.tex
pdflatex yangMillsTestSetupStrategy.tex
```

## The Problem

**Yang-Mills Existence and Mass Gap:** Prove that for any compact simple gauge group G, a non-trivial quantum Yang-Mills theory exists on ℝ⁴ and has a mass gap Δ > 0.

### What This Means

- **Existence**: Rigorously construct 4D Yang-Mills QFT satisfying Wightman or Osterwalder-Schrader axioms
- **Mass Gap**: Show spectrum(H) ∩ (0,Δ) = ∅ for some Δ > 0 (energy gap above ground state)
- **Physical Significance**: Explains why gluons confine quarks and why the strong force is short-ranged

## Mathematical Prerequisites

### Core Topics to Master

1. **Differential Geometry**
   - Manifolds and fiber bundles
   - Lie groups: SU(N), SO(N), Sp(N)
   - Principal bundles and connections
   - Curvature: F = dA + A ∧ A

2. **Functional Analysis**
   - Hilbert spaces and operators
   - Self-adjoint operators and spectrum
   - Spectral theory
   - Sobolev spaces

3. **Quantum Field Theory**
   - Wightman axioms
   - Osterwalder-Schrader axioms
   - Reflection positivity
   - Renormalization theory

4. **Lattice Methods**
   - Wilson lattice gauge theory
   - Monte Carlo simulations
   - Continuum limit
   - Finite-size scaling

## Current Status

### ✅ Completed

- [x] Formalized basic structures in Lean
- [x] Created test framework
- [x] Set up project structure
- [x] SU(2) property verification
- [x] LaTeX documentation

### 🔨 In Progress

- [ ] Implement lattice gauge theory simulation
- [ ] Study 2D/3D known results
- [ ] Understand asymptotic freedom
- [ ] Learn renormalization group methods

### 📝 TODO

- [ ] Implement Wilson action on lattice
- [ ] Monte Carlo algorithm (Metropolis)
- [ ] Measure Wilson loops
- [ ] Compute correlation functions
- [ ] Finite-size scaling analysis

## Resources

### Key Papers

- Jaffe & Witten: "Quantum Yang-Mills Theory" (Clay Millennium Problem description)
- Gross & Wilczek: "Ultraviolet behavior of non-abelian gauge theories" (asymptotic freedom)
- Wilson: "Quarks and strings on a lattice" (lattice gauge theory)
- Balaban: "Renormalization group approach to lattice gauge field theories"

### Books

- Streater & Wightman: "PCT, Spin and Statistics, and All That"
- Glimm & Jaffe: "Quantum Physics: A Functional Integral Point of View"
- Peskin & Schroeder: "An Introduction to Quantum Field Theory"
- Montvay & Münster: "Quantum Fields on a Lattice"

### Online Resources

- Clay Mathematics Institute: https://www.claymath.org/millennium/yang-mills-mass-gap/
- Lean Zulip: https://leanprover.zulipchat.com/
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/

## Notes

⚠️ **Important**: This is research-level mathematics. The problem has been unsolved for over 50 years. The goal is to:
1. Understand the problem deeply
2. Learn the mathematical tools
3. Contribute computational evidence
4. Maybe find new approaches

Don't expect to solve it quickly (or at all)! The value is in the learning process.

## Next Steps

1. **Week 1**: Run SU(2) tests, understand Pauli matrices
2. **Week 2**: Implement simple 2D Ising model (warm-up)
3. **Week 3**: Study Wilson lattice action
4. **Week 4**: Begin lattice gauge theory simulation

## License

Research notes and code: MIT or Apache 2.0
Academic content: Fair use for educational purposes

---

Last updated: 2025-10-23
