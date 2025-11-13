"""
Geometric Scaling Algorithm: Inscribed Circle in Square

Given a square with inscribed circle of radius r, the diagonal from center 
to corner is r√2, which becomes the new radius for the next iteration.

This creates a geometric sequence where radius grows as: r₀ * (√2)ⁿ
"""

using Printf

"""
    SquareWithInscribedCircle

Structure to hold a square configuration with its inscribed circle.

# Fields
- `radius::Float64`: The radius of the inscribed circle
"""
struct SquareWithInscribedCircle
    radius::Float64
    
    # Inner constructor to ensure radius is positive
    function SquareWithInscribedCircle(radius::Float64)
        if radius <= 0
            error("Radius must be positive, got: $radius")
        end
        new(radius)
    end
end

# Convenience constructor for integer input
SquareWithInscribedCircle(radius::Int) = SquareWithInscribedCircle(Float64(radius))

"""
    square_side_length(config::SquareWithInscribedCircle)

Calculate the side length of the square (diameter of inscribed circle).
"""
function square_side_length(config::SquareWithInscribedCircle)
    return 2 * config.radius
end

"""
    diagonal_to_corner(config::SquareWithInscribedCircle)

Calculate the diagonal from center to corner of the square.
For a square with inscribed circle of radius r, this equals r√2.
"""
function diagonal_to_corner(config::SquareWithInscribedCircle)
    return sqrt(config.radius^2 + config.radius^2)
end

"""
    scale_once(config::SquareWithInscribedCircle)

Perform one iteration of geometric scaling.
The new radius becomes the old diagonal (multiplies by √2).
"""
function scale_once(config::SquareWithInscribedCircle)
    new_radius = config.radius * sqrt(2)
    return SquareWithInscribedCircle(new_radius)
end

"""
    scale_n_times(config::SquareWithInscribedCircle, n::Int)

Apply scaling n times iteratively.

# Arguments
- `config`: Initial configuration
- `n`: Number of iterations

# Returns
- `SquareWithInscribedCircle`: Configuration after n iterations
"""
function scale_n_times(config::SquareWithInscribedCircle, n::Int)
    if n < 0
        error("Number of iterations must be non-negative, got: $n")
    end
    
    current = config
    for _ in 1:n
        current = scale_once(current)
    end
    return current
end

"""
    scale_n_times_formula(initial_radius::Float64, n::Int)

Calculate radius after n iterations using the closed-form formula.
Formula: radius_n = initial_radius * (√2)ⁿ

This is faster for large n than iterative scaling.
"""
function scale_n_times_formula(initial_radius::Float64, n::Int)
    if initial_radius <= 0
        error("Initial radius must be positive")
    end
    if n < 0
        error("Number of iterations must be non-negative")
    end
    
    return initial_radius * (sqrt(2))^n
end

"""
    print_scaling_sequence(initial_radius::Float64, max_iterations::Int)

Print the scaling sequence for visualization.

# Arguments
- `initial_radius`: Starting radius
- `max_iterations`: Number of iterations to display
"""
function print_scaling_sequence(initial_radius::Float64, max_iterations::Int)
    println("="^60)
    println("Geometric Scaling Sequence")
    println("Initial radius: $initial_radius")
    println("Scaling factor: √2 ≈ $(sqrt(2))")
    println("="^60)
    println()
    
    @printf("%-10s %-20s %-20s %-20s\n", "Iteration", "Radius", "Side Length", "Diagonal")
    println("-"^70)
    
    config = SquareWithInscribedCircle(initial_radius)
    
    for i in 0:max_iterations
        radius = config.radius
        side = square_side_length(config)
        diag = diagonal_to_corner(config)
        
        @printf("%-10d %-20.6f %-20.6f %-20.6f\n", i, radius, side, diag)
        
        if i < max_iterations
            config = scale_once(config)
        end
    end
    
    println()
    println("Formula verification for iteration $max_iterations:")
    formula_result = scale_n_times_formula(initial_radius, max_iterations)
    @printf("Using formula: %.6f\n", formula_result)
    @printf("Using iteration: %.6f\n", config.radius)
    @printf("Difference: %.2e\n", abs(formula_result - config.radius))
end

"""
    plot_scaling_growth(initial_radius::Float64, max_iterations::Int)

Generate data for plotting (returns arrays of iterations and radii).
Use with your favorite plotting library (Plots.jl, Makie.jl, etc.)
"""
function plot_scaling_growth(initial_radius::Float64, max_iterations::Int)
    iterations = 0:max_iterations
    radii = [scale_n_times_formula(initial_radius, n) for n in iterations]
    return iterations, radii
end

# Example usage and tests
function run_examples()
    println("\n" * "="^60)
    println("Example 1: Starting with radius 5 (as in Lean formalization)")
    println("="^60)
    print_scaling_sequence(5.0, 10)
    
    println("\n" * "="^60)
    println("Example 2: Verify geometric growth property")
    println("="^60)
    config0 = SquareWithInscribedCircle(5.0)
    config1 = scale_once(config0)
    config2 = scale_once(config1)
    
    ratio1 = config1.radius / config0.radius
    ratio2 = config2.radius / config1.radius
    
    println("Radius at iteration 0: $(config0.radius)")
    println("Radius at iteration 1: $(config1.radius)")
    println("Radius at iteration 2: $(config2.radius)")
    println()
    println("Ratio (iteration 1 / iteration 0): $ratio1")
    println("Ratio (iteration 2 / iteration 1): $ratio2")
    println("√2 = $(sqrt(2))")
    println("Constant ratio confirmed: ", isapprox(ratio1, sqrt(2), rtol=1e-10))
    
    println("\n" * "="^60)
    println("Example 3: Large iteration using formula")
    println("="^60)
    n = 100
    result = scale_n_times_formula(5.0, n)
    @printf("After %d iterations: radius = %.6e\n", n, result)
    @printf("This is 5 × (√2)^%d\n", n)
end

# Run examples if this file is executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    run_examples()
end

