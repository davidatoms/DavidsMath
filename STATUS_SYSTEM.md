# File Status System

This repository uses a status labeling system to clearly indicate the nature and validation level of each file.

## Status Types

### VALIDATED
- **Meaning**: Computationally verified, formally proven, or experimentally confirmed
- **Examples**: 
  - Proofs completed in Lean with no `sorry`
  - Computational results validated against experimental data
  - Mathematical relationships confirmed through multiple methods
- **Files**: Core √2 scaling framework, quantum-geometric duality

### EXPLORATORY
- **Meaning**: Investigation of open problems or unproven ideas
- **Examples**:
  - Work on Millennium Prize Problems (Hodge, Yang-Mills)
  - Novel approaches to unsolved problems
  - Speculative but mathematically grounded research
- **Note**: These are research directions, not claimed solutions
- **Files**: Hodge Conjecture, Yang-Mills theory, Poincaré Conjecture formalization

### IN_PROGRESS
- **Meaning**: Active development, definitions and initial theorems
- **Examples**:
  - Ongoing research with partial results
  - Work that's being actively developed
  - Early-stage investigations
- **Files**: Geometric Complexity Theory

## Status Header Format

Each file should have a status header at the top:

```lean
-- Status: VALIDATED | EXPLORATORY | IN_PROGRESS
-- Domain: [Topic Area]
-- Description: [One sentence summary]
-- Validation: [How it's validated, if applicable]
-- Note: [Any important notes]
-- References: [Relevant papers, docs, or files]
```

## Benefits

- **Clarity**: Immediately see what's proven vs exploratory
- **Credibility**: Honest about what's validated vs what's research
- **Organization**: Easy to filter by status
- **Transparency**: Shows the research process

## Usage

When viewing files:
- Start with **VALIDATED** files for proven results
- Review **IN_PROGRESS** for active work
- Explore **EXPLORATORY** for research directions

When adding new files:
- Always include a status header
- Be honest about validation level
- Update status as work progresses

---

**This system helps maintain the "workbook" nature of the repository** - showing both validated findings and ongoing exploration.

