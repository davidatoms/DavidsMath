# WARP.md

This file provides guidance to WARP (warp.dev) when working with code in this repository.

## Project Overview

This is a mathematical research repository focused on the Yang-Mills Mass Gap Problem (one of the seven Millennium Prize Problems worth $1,000,000). The project combines:

- **Lean 4 formalizations** of mathematical physics concepts
- **Computational simulations** for lattice gauge theory
- **Research notes** on differential geometry, quantum field theory, and functional analysis
- **LaTeX documentation** of mathematical prerequisites

The repository contains diverse mathematical explorations including Yang-Mills theory, Hodge conjecture, Minkowski space, Cobb-Douglas economics models, and various physics simulations.

## Repository Structure

```
DavidsMath/
├── DavidsMath/              # Lean 4 library modules (30+ .lean files)
│   ├── YangMills*.lean      # Yang-Mills theory formalizations
│   ├── HodgeConjecture.lean # Hodge conjecture formalization
│   ├── MinkowskiSpace.lean  # Spacetime geometry
│   ├── CobbDouglas*.lean    # Economic models
│   └── [Various physics/math formalizations]
│
├── code/
│   ├── simulations/         # Lattice gauge theory simulations
│   ├── visualization/       # Plotting tools
│   └── tests/
│       ├── test_su2_gauge_group.py  # SU(2) gauge group verification
│       └── test_su3_gauge_group.py  # SU(3) gauge group verification
│
├── notes/
│   ├── differential_geometry/
│   ├── functional_analysis/
│   ├── qft/
│   ├── lattice_theory/
│   └── study_plan/
│       └── learning_roadmap.md  # 16-week learning plan
│
├── proofs/attempts/         # Proof strategies and attempts
│
├── pythonScripts/          # Various Python utilities
│   ├── thurstonsGeometrization.py
│   ├── minkowskiAdams.py
│   └── make_copy_of_lean_math_and_translate_to_latex.py
│
├── matlabScripts/          # MATLAB scripts
│   ├── ricciFlow.m
│   └── ricci_flow_sphere.mlx
│
├── tex/                    # LaTeX documentation
│   ├── yangMillsMathematicalPrerequisites.tex
│   └── yangMillsTestSetupStrategy.tex
│
└── markdown/               # Additional markdown notes
```

## Build and Test Commands

### Lean 4 Development

**Build entire library:**
```bash
lake build
```

**Build specific modules:**
```bash
lake build DavidsMath.YangMillsMinimal
lake build DavidsMath.YangMillsTestStrategy
lake build DavidsMath.HodgeConjecture
```

**Lean version:** v4.24.0 (specified in `lean-toolchain`)

**Dependencies:**
- mathlib4 (from https://github.com/leanprover-community/mathlib4.git)

### Python Testing

**Run SU(2) gauge group tests:**
```bash
cd code/tests
python3 test_su2_gauge_group.py
```

**Run SU(3) gauge group tests:**
```bash
cd code/tests
python3 test_su3_gauge_group.py
```

**Python environment:** Use `pythonScripts/venv/` for isolated Python environment

### LaTeX Compilation

```bash
cd tex
pdflatex yangMillsMathematicalPrerequisites.tex
pdflatex yangMillsTestSetupStrategy.tex
```

### MATLAB Scripts

```bash
cd matlabScripts
matlab -batch "run('ricciFlow.m')"
```

## Architecture and Key Concepts

### Lean 4 Formalization Strategy

The Lean modules follow a hierarchical dependency structure:

1. **Foundation Layer**: `DavidsMath.Basic`, `MinkowskiSpace.lean`
2. **Mathematical Physics**: `YangMills*.lean` files (8 variants exploring different formalization approaches)
3. **Advanced Topics**: `HodgeConjecture.lean`, `RepresentationTheory.lean`, `AlgebraicTopology.lean`
4. **Computational Models**: `CobbDouglas*.lean`, `Boltzmann.lean`, `ChuaCircuit.lean`

**Key Lean files:**
- `YangMills.lean` - Main formalization using mathlib's differential geometry and Lie theory
- `YangMillsDependencies.lean` - Core dependencies
- `YangMillsMinimal.lean` - Simplified, buildable version
- `YangMillsTestStrategy.lean` - Test framework for verification
- `YangMillsPrerequisites.lean` - Full mathematical prerequisites

### Yang-Mills Project Specific Notes

**The Problem:** Prove that for any compact simple gauge group G, a non-trivial quantum Yang-Mills theory exists on ℝ⁴ and has a mass gap Δ > 0.

**Current Implementation Status:**
- ✓ SU(2) gauge group properties verified computationally
- ✓ Pauli matrices and Lie algebra commutation relations tested
- ✓ Basic Lean formalizations compile successfully
- ⧖ Lattice gauge theory simulations (in progress)
- ⧖ Monte Carlo methods for observables (planned)

**Mathematical Prerequisites Being Studied:**
1. Lie groups and algebras (SU(N), SO(N))
2. Principal bundles and connections
3. Functional analysis (Hilbert spaces, spectral theory)
4. Axiomatic QFT (Wightman axioms, Osterwalder-Schrader axioms)

## Development Workflow

### For Lean Development

1. The main library entry point is `DavidsMath.lean` which imports core modules
2. New mathematical formalizations should be added as separate `.lean` files in `DavidsMath/`
3. Run `lake build` after making changes to verify compilation
4. The project uses mathlib4's existing differential geometry, Lie theory, and manifold structures

### For Computational Work

1. Python tests verify mathematical properties of gauge groups
2. Tests use NumPy for matrix operations and numerical verification
3. Results should match theoretical predictions from Lie algebra theory
4. New simulations go in `code/simulations/`

### For Research Notes

1. Notes are organized by mathematical subdiscipline
2. Follow the 16-week learning roadmap in `notes/study_plan/learning_roadmap.md`
3. LaTeX documents in `tex/` provide comprehensive mathematical references

## Important Files

- `lakefile.toml` - Lean project configuration
- `lean-toolchain` - Specifies Lean version (v4.24.0)
- `YANG_MILLS_README.md` - Yang-Mills project overview and next steps
- `SETUP_COMPLETE.md` - Project setup documentation and weekly plan
- `lake-manifest.json` - Lake package manager lock file

## CI/CD

GitHub Actions workflow (`.github/workflows/lean_action_ci.yml`) automatically:
- Builds all Lean code on push/PR
- Verifies compilation using leanprover/lean-action@v1

## Notes for AI Assistants

- This is research-level mathematics; the Yang-Mills Mass Gap problem is unsolved for 50+ years
- When working with Lean code, be aware that some modules use `sorry` as placeholders for complex proofs
- The project explores multiple formalization approaches (hence many YangMills*.lean variants)
- Python scripts use scientific computing libraries (NumPy, SciPy) for numerical verification
- MATLAB scripts focus on geometric flows and visualizations
- The project intentionally combines rigorous formal proof (Lean) with computational verification (Python/MATLAB)
