# Geometric Scaling Algorithm - Julia Implementation

## Overview

Implementation of a geometric algorithm that scales a circle inscribed in a square by factor √2 per iteration.

## Algorithm

```
Input: Initial radius r₀, number of iterations n
1. Start with circle of radius r inscribed in square of side 2r
2. Compute diagonal: d = √(r² + r²) = r√2
3. Set new radius: r' = d
4. Repeat for n iterations
Output: r_n = r₀(√2)^n
```

## Files

### Core Implementations
- `scaling_algorithm_inscribed_circle.jl` - Basic algorithm implementation
- `quantum_geometric_scaling.jl` - Analysis of geometric properties
- `derivative_analysis.jl` - Derivative computation and analysis

### Visualizations
- `visualizations.jl` - Generates 7 static PNG plots
- `create_animation.jl` - Generates 4 animated GIF visualizations
- `graphs/` - Output directory for all generated images

## Usage

```bash
# Generate all static visualizations
julia visualizations.jl

# Generate all animations
julia create_animation.jl

# Run derivative analysis
julia derivative_analysis.jl
```

## Mathematical Properties

### Proven in Lean
- Scaling formula: r_n = r₀(√2)^n
- Geometric growth of side length
- See `../DavidsMath/1ScalingAlgorithmInscribedCircleSquare.lean`

### Verified Numerically
- Derivative ratio: d^(k+1)r / d^k r = ln(√2) ≈ 0.3466
- Area efficiency: π/4 ≈ 0.7854 (constant across scales)
- Inverse relationship: (√2)^n × (1/√2)^n = 1

## Dependencies

- Julia 1.x
- Plots.jl
- Printf (standard library)
