# Yang-Mills Mass Gap - Learning Roadmap

## Phase 1: Foundations (Weeks 1-4)

### Week 1: Lie Groups & Algebras
- [ ] Study SU(2) in detail
  - Run `test_su2_gauge_group.py`
  - Understand Pauli matrices
  - Derive commutation relations
- [ ] Learn SU(3) (for QCD)
  - Gell-Mann matrices
  - Color charge
- [ ] General Lie group theory
  - Exponential map
  - Adjoint representation
  - Structure constants

**Resources:**
- Brian Hall: "Lie Groups, Lie Algebras, and Representations"
- Chapter 2 of `yangMillsMathematicalPrerequisites.tex`

### Week 2: Differential Geometry
- [ ] Manifolds and tangent bundles
- [ ] Fiber bundles
- [ ] Principal G-bundles
- [ ] Connections on bundles
- [ ] Curvature F = dA + A ∧ A

**Resources:**
- Nakahara: "Geometry, Topology and Physics"
- Baez & Muniain: "Gauge Fields, Knots and Gravity"

### Week 3: Functional Analysis
- [ ] Hilbert spaces
- [ ] Bounded vs unbounded operators
- [ ] Self-adjoint operators
- [ ] Spectral theorem
- [ ] Domain issues

**Resources:**
- Reed & Simon: "Methods of Modern Mathematical Physics"
- Sections on Sobolev spaces

### Week 4: Basic QFT
- [ ] Free scalar field
- [ ] Canonical quantization
- [ ] Fock space construction
- [ ] Creation/annihilation operators
- [ ] Correlation functions

**Resources:**
- Peskin & Schroeder: Chapters 2-3
- `yangMillsQuantumGapQuantumField.md`

## Phase 2: Yang-Mills Theory (Weeks 5-8)

### Week 5: Classical Yang-Mills
- [ ] Yang-Mills Lagrangian
- [ ] Gauge transformations
- [ ] Equations of motion
- [ ] Gauge fixing
- [ ] Faddeev-Popov ghosts

**Resources:**
- `yangMillsQuantumGapYangMillsTheory.md`
- Ramond: "Field Theory: A Modern Primer"

### Week 6: Quantization
- [ ] Path integral formulation
- [ ] Functional integral
- [ ] BRST symmetry
- [ ] Ward identities
- [ ] Perturbation theory

**Resources:**
- Weinberg: "The Quantum Theory of Fields" Vol 2
- Peskin & Schroeder: Chapter 16

### Week 7: Renormalization
- [ ] UV divergences
- [ ] Counterterms
- [ ] Running coupling constant
- [ ] β-function
- [ ] Asymptotic freedom

**Resources:**
- Gross & Wilczek paper
- Collins: "Renormalization"

### Week 8: Axiomatic QFT
- [ ] Wightman axioms
- [ ] Osterwalder-Schrader axioms
- [ ] Reflection positivity
- [ ] Reconstructi
on theorem
- [ ] Mass gap definition

**Resources:**
- Streater & Wightman book
- `yangMillsQuantumGapProblem.md`

## Phase 3: Computational Methods (Weeks 9-12)

### Week 9: Lattice Basics
- [ ] Discretize spacetime
- [ ] Wilson action
- [ ] Plaquette variables
- [ ] Strong/weak coupling limits
- [ ] Reflection positivity on lattice

**Resources:**
- Montvay & Münster: "Quantum Fields on a Lattice"
- Wilson's original paper

### Week 10: Monte Carlo
- [ ] Metropolis algorithm
- [ ] Heat bath algorithm
- [ ] Thermalization
- [ ] Autocorrelation
- [ ] Error estimation

**Action Items:**
- Implement 2D Ising model first (warm-up)
- Then 4D SU(2) gauge theory

### Week 11: Observables
- [ ] Wilson loops
- [ ] String tension
- [ ] Correlation functions
- [ ] Mass extraction
- [ ] Glueball spectrum

**Code to Write:**
```python
# code/simulations/wilson_loops.py
# code/simulations/correlators.py
# code/simulations/mass_extraction.py
```

### Week 12: Analysis
- [ ] Finite-size scaling
- [ ] Continuum extrapolation
- [ ] Volume dependence
- [ ] Mass gap estimates
- [ ] Error analysis

## Phase 4: Advanced Topics (Weeks 13-16)

### Week 13: Constructive QFT
- [ ] φ⁴ in 2D (known results)
- [ ] φ⁴ in 3D
- [ ] 2D Abelian Higgs model
- [ ] Cluster expansions
- [ ] Convergence proofs

**Resources:**
- Glimm & Jaffe book
- `yangMillsQuantumGapMathematicalPerspective.md`

### Week 14: Known Partial Results
- [ ] Balaban's 3D results
- [ ] Balaban's 4D program
- [ ] Gauge fixing techniques
- [ ] Renormalization group approach
- [ ] Current status of proofs

### Week 15: Confinement
- [ ] Wilson loop criterion
- [ ] Area law vs perimeter law
- [ ] String tension
- [ ] Glueball masses
- [ ] Relation to mass gap

### Week 16: Open Questions
- [ ] Review Millennium problem statement
- [ ] Survey of approaches
- [ ] What's missing?
- [ ] Possible strategies
- [ ] Your own ideas!

## Ongoing Activities

### Every Week:
- [ ] Read 1-2 papers
- [ ] Work through exercises
- [ ] Code something new
- [ ] Take notes in markdown
- [ ] Update research log

### Monthly:
- [ ] Review progress
- [ ] Adjust learning plan
- [ ] Write summary notes
- [ ] Share findings (blog/notes)

## Assessment Checkpoints

### After Phase 1:
Can you:
- [ ] Explain SU(2) and SU(3) structure?
- [ ] Compute commutation relations?
- [ ] Understand fiber bundles?
- [ ] Define spectral gap?

### After Phase 2:
Can you:
- [ ] Write down Yang-Mills Lagrangian?
- [ ] Explain asymptotic freedom?
- [ ] State Wightman axioms?
- [ ] Understand the mass gap problem?

### After Phase 3:
Can you:
- [ ] Implement Wilson action?
- [ ] Run Monte Carlo simulation?
- [ ] Measure Wilson loops?
- [ ] Extract mass from correlators?

### After Phase 4:
Can you:
- [ ] Explain Balaban's approach?
- [ ] Discuss confinement mechanisms?
- [ ] Critique existing approaches?
- [ ] Propose research directions?

## Resources by Phase

### Online Courses:
- MIT OCW: Quantum Field Theory (8.323, 8.324)
- Stanford: Leonard Susskind's lectures
- David Tong's lecture notes
- Tobias Osborne's QFT course

### Software:
- SciPy/NumPy (Python)
- MILC (lattice QCD code)
- Chroma (lattice QCD toolkit)
- Lean 4 (formal verification)

### Communities:
- Physics Stack Exchange
- Lean Zulip chat
- arXiv (hep-lat, hep-th, math-ph)
- Clay Mathematics Institute

## Notes

- This is a **multi-year** project
- Adjust pace based on your background
- It's okay to skip or reorder
- Focus on understanding, not speed
- Ask questions, lots of questions!

---

Remember: The journey is the destination. Even professional physicists find this difficult!
