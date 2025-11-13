# Visualizations

Generated visualizations for geometric scaling algorithm.

## Static Images (PNG)

### 1. geometric_scaling_sequence.png
12 iterations showing circle inscribed in square at each step.
- Blue: Square (constraint domain)
- Red: Circle (inscribed state space)
- Green: Diagonal (next radius)

### 2. radius_growth.png
Radius growth over iterations on linear and log scales.
- Formula: r_n = r₀(√2)^n
- Log scale shows straight line (confirms exponential growth)

### 3. area_expansion.png
Circle area vs square area over iterations.
- Left: Both areas (log scale)
- Right: Efficiency ratio = π/4 (constant)

### 4. quantum_connection.png
Geometric scaling vs quantum normalization.
- Top left: (√2)^n (growing)
- Top right: (1/√2)^n (shrinking)
- Bottom: Product = 1 (inverse relationship)

### 5. phase_space_nested.png
Nested circles and squares (6 layers).
- Each layer scaled by √2 from previous
- Visualizes hierarchical structure

### 6. domain_states_relationship.png
Relationship between domain size and state radius.
- Top left: r = domain/2
- Top right: Area = π(domain/2)²
- Bottom left: domain = 2r (inverse)

### 7. derivative_analysis.png
Derivatives of radius function.
- Top left: All derivatives (log scale)
- Top right: Derivative ratios = ln(√2)
- Bottom left: Area expansion rate
- Bottom right: Velocity vector field

## Animated Images (GIF)

### 1. geometric_scaling_animation.gif
Core algorithm, 11 frames (iterations 0-10).
Shows square, circle, diagonal at each step.

### 2. velocity_field_animation.gif
First derivative as radial velocity vectors.
12 arrows showing dr/dn in all directions.

### 3. quantum_geometric_duality_animation.gif
Side-by-side: (√2)^n growing, (1/√2)^n shrinking.
Product = 1 displayed each frame.

### 4. growth_comparison_animation.gif
Exponential vs linear vs quadratic growth comparison.

## Regeneration

```bash
# Static images
julia ../visualizations.jl

# Animations
julia ../create_animation.jl
```

All images saved to this directory automatically.
