"""
Derivative Analysis of Geometric-Quantum Scaling

Explores first, second, and third derivatives of the scaling function.

Key Insight: First and second derivatives should be absolute values because
the "area of possibility through which empty space is observed can go in 
multiple directions" - possibilities expand radially in all directions.
"""

using Printf
using Plots

include("scaling_algorithm_inscribed_circle.jl")

"""
    radius_function(r0::Float64, n::Float64)

The continuous scaling function: r(n) = r₀ × (√2)ⁿ
where n can be any real number (continuous iteration parameter).
"""
function radius_function(r0::Float64, n::Float64)
    return r0 * (sqrt(2))^n
end

"""
    first_derivative(r0::Float64, n::Float64)

First derivative: dr/dn = r₀ × (√2)ⁿ × ln(√2)

Physical meaning:
- Rate of expansion of possibility space
- Velocity of state space growth
- How fast uncertainty region is expanding
"""
function first_derivative(r0::Float64, n::Float64)
    # dr/dn = r₀ × (√2)ⁿ × ln(√2)
    return r0 * (sqrt(2))^n * log(sqrt(2))
end

"""
    second_derivative(r0::Float64, n::Float64)

Second derivative: d²r/dn² = r₀ × (√2)ⁿ × [ln(√2)]²

Physical meaning:
- Acceleration of expansion
- How the growth rate itself is changing
- Curvature of the expansion trajectory
"""
function second_derivative(r0::Float64, n::Float64)
    # d²r/dn² = r₀ × (√2)ⁿ × [ln(√2)]²
    return r0 * (sqrt(2))^n * (log(sqrt(2)))^2
end

"""
    third_derivative(r0::Float64, n::Float64)

Third derivative: d³r/dn³ = r₀ × (√2)ⁿ × [ln(√2)]³

Physical meaning:
- Jerk (rate of change of acceleration)
- How smoothly the expansion accelerates
- Third-order dynamics of state space growth
"""
function third_derivative(r0::Float64, n::Float64)
    # d³r/dn³ = r₀ × (√2)ⁿ × [ln(√2)]³
    return r0 * (sqrt(2))^n * (log(sqrt(2)))^3
end

"""
    directional_derivative_magnitude(r0::Float64, n::Float64)

Since possibilities expand in ALL directions (radially), we need the magnitude.
The total rate of area expansion in the 2D plane.

For circle area A = πr², dA/dn = 2πr × dr/dn
This captures expansion in all directions simultaneously.
"""
function directional_derivative_magnitude(r0::Float64, n::Float64)
    r = radius_function(r0, n)
    dr_dn = first_derivative(r0, n)
    # Area = πr², so dA/dn = 2πr × dr/dn
    return 2 * π * r * dr_dn
end

"""
    multidirectional_expansion_analysis(r0::Float64, n_max::Int)

Analyze how the expansion happens in multiple directions.
"""
function multidirectional_expansion_analysis(r0::Float64, n_max::Int)
    println("="^80)
    println("MULTIDIRECTIONAL EXPANSION ANALYSIS")
    println("="^80)
    println("\nKey Insight: Space expands in ALL directions, not just one!")
    println("We measure ABSOLUTE values because direction is arbitrary.")
    println()
    
    @printf("%-8s %-15s %-15s %-15s %-15s %-15s\n",
            "n", "r(n)", "|dr/dn|", "|d²r/dn²|", "|d³r/dn³|", "Area Rate")
    println("-"^95)
    
    for n in 0:n_max
        r = radius_function(r0, Float64(n))
        dr = abs(first_derivative(r0, Float64(n)))
        d2r = abs(second_derivative(r0, Float64(n)))
        d3r = abs(third_derivative(r0, Float64(n)))
        area_rate = abs(directional_derivative_magnitude(r0, Float64(n)))
        
        @printf("%-8d %-15.6f %-15.6f %-15.6f %-15.6f %-15.6f\n",
                n, r, dr, d2r, d3r, area_rate)
    end
    
    println()
    println("OBSERVATIONS:")
    println("1. All derivatives grow exponentially (like radius itself)")
    println("2. We use ABSOLUTE values because expansion is radial (all directions)")
    println("3. Ratios between consecutive derivatives reveal fundamental constants")
    println()
end

"""
    derivative_ratios_analysis(r0::Float64, n::Float64)

Analyze the ratios between derivatives - reveals fundamental structure.
"""
function derivative_ratios_analysis(r0::Float64, n::Float64)
    r = radius_function(r0, n)
    dr = first_derivative(r0, n)
    d2r = second_derivative(r0, n)
    d3r = third_derivative(r0, n)
    
    println("="^80)
    println("DERIVATIVE RATIOS AT n = $n")
    println("="^80)
    println()
    
    println("Values:")
    @printf("  r(n)      = %.10f\n", r)
    @printf("  dr/dn     = %.10f\n", dr)
    @printf("  d²r/dn²   = %.10f\n", d2r)
    @printf("  d³r/dn³   = %.10f\n", d3r)
    println()
    
    println("Ratios:")
    @printf("  (dr/dn) / r           = %.10f\n", dr/r)
    @printf("  (d²r/dn²) / (dr/dn)   = %.10f\n", d2r/dr)
    @printf("  (d³r/dn³) / (d²r/dn²) = %.10f\n", d3r/d2r)
    println()
    
    ln_sqrt2 = log(sqrt(2))
    println("Fundamental Constant: ln(√2) = $ln_sqrt2")
    println()
    println("KEY INSIGHT:")
    println("  Each ratio equals ln(√2) ≈ 0.3466")
    println("  This is INDEPENDENT of n and r₀!")
    println("  This is a UNIVERSAL constant of the system.")
    println()
end

"""
    velocity_acceleration_jerk_interpretation()

Physical interpretation as velocity, acceleration, and jerk.
"""
function velocity_acceleration_jerk_interpretation()
    println("="^80)
    println("PHYSICAL INTERPRETATION: Velocity, Acceleration, Jerk")
    println("="^80)
    println()
    
    println("If we think of 'n' as TIME (or iteration time):")
    println()
    println("1. POSITION: r(n) = r₀(√2)ⁿ")
    println("   → Where the possibility boundary is")
    println("   → Size of accessible state space")
    println()
    println("2. VELOCITY: dr/dn = r₀(√2)ⁿ ln(√2)")
    println("   → How fast the boundary is expanding")
    println("   → Rate of state space growth")
    println("   → Expansion velocity in ALL directions")
    println()
    println("3. ACCELERATION: d²r/dn² = r₀(√2)ⁿ [ln(√2)]²")
    println("   → How the expansion rate changes")
    println("   → Positive: exponential growth accelerates")
    println("   → Like cosmic expansion or compound interest")
    println()
    println("4. JERK: d³r/dn³ = r₀(√2)ⁿ [ln(√2)]³")
    println("   → Smoothness of the acceleration")
    println("   → Positive: smooth, continuous acceleration")
    println("   → No sudden jumps in dynamics")
    println()
    
    println("QUANTUM ANALOGY:")
    println("  Position → State localization")
    println("  Velocity → Momentum uncertainty growth")
    println("  Acceleration → Energy level spacing change")
    println("  Jerk → Transition rate dynamics")
    println()
end

"""
    radial_vs_tangential_analysis(r0::Float64, n::Float64)

Analyze radial (outward) vs tangential (circular) expansion.
"""
function radial_vs_tangential_analysis(r0::Float64, n::Float64)
    println("="^80)
    println("RADIAL vs TANGENTIAL EXPANSION")
    println("="^80)
    println()
    println("Your insight: 'Empty space observed in multiple directions'")
    println()
    
    r = radius_function(r0, n)
    dr_dn = first_derivative(r0, n)
    
    # Radial expansion (outward)
    radial_expansion = dr_dn
    
    # Tangential: circumference growth
    # C = 2πr, so dC/dn = 2π × dr/dn
    tangential_expansion = 2 * π * dr_dn
    
    # Area expansion (captures both)
    # A = πr², so dA/dn = 2πr × dr/dn
    area_expansion = 2 * π * r * dr_dn
    
    println("At iteration n = $n:")
    @printf("  Radius: %.6f\n\n", r)
    
    println("Expansion Rates:")
    @printf("  Radial (outward):     %.6f\n", radial_expansion)
    @printf("  Tangential (around):  %.6f\n", tangential_expansion)
    @printf("  Area (total 2D):      %.6f\n\n", area_expansion)
    
    println("Interpretation:")
    println("  • Radial: How fast we move outward from center")
    println("  • Tangential: How fast the perimeter grows")
    println("  • Area: Total growth of possibility space")
    println()
    println("All three POSITIVE and GROWING - expansion in all directions!")
    println()
end

"""
    quantum_derivatives_connection()

Connect derivatives to quantum mechanical quantities.
"""
function quantum_derivatives_connection()
    println("="^80)
    println("DERIVATIVES ↔ QUANTUM MECHANICS")
    println("="^80)
    println()
    
    println("CONNECTIONS:")
    println()
    println("1. POSITION → WAVEFUNCTION SUPPORT")
    println("   r(n) ↔ Size of region where ψ(x) is non-negligible")
    println("   Larger n → More spread out wavefunction")
    println()
    println("2. VELOCITY → MOMENTUM UNCERTAINTY")
    println("   dr/dn ↔ dΔx/dt in uncertainty principle")
    println("   ΔxΔp ≥ ℏ/2, as Δx grows (r grows), momentum uncertainty grows")
    println()
    println("3. ACCELERATION → ENERGY LEVEL STRUCTURE")
    println("   d²r/dn² ↔ How energy level spacing changes")
    println("   Positive acceleration → Levels get farther apart (like harmonic oscillator)")
    println()
    println("4. JERK → TRANSITION DYNAMICS")
    println("   d³r/dn³ ↔ How transition rates between levels change")
    println("   Smooth jerk → Smooth quantum evolution")
    println()
    
    println("THE √2 SCALING IN DERIVATIVES:")
    println()
    println("  Each derivative contains (√2)ⁿ factor")
    println("  This is the SAME as quantum gate scaling!")
    println("  Hadamard gate: creates superposition with 1/√2")
    println("  Our expansion: geometric growth with √2")
    println("  They're DUAL processes!")
    println()
end

"""
    test_derivative_properties(r0::Float64 = 5.0)

Run all derivative tests and analyses.
"""
function test_derivative_properties(r0::Float64 = 5.0)
    println("\n" * "="^80)
    println("DERIVATIVE ANALYSIS OF GEOMETRIC-QUANTUM SCALING")
    println("Initial radius: r₀ = $r0")
    println("="^80)
    println()
    
    # Basic analysis
    multidirectional_expansion_analysis(r0, 10)
    
    # Ratio analysis
    derivative_ratios_analysis(r0, 5.0)
    
    # Physical interpretation
    velocity_acceleration_jerk_interpretation()
    
    # Directional analysis
    radial_vs_tangential_analysis(r0, 5.0)
    
    # Quantum connection
    quantum_derivatives_connection()
end

"""
    plot_derivative_analysis(r0::Float64 = 5.0; save_path="graphs/")

Create visualizations of derivatives.
"""
function plot_derivative_analysis(r0::Float64 = 5.0; save_path="graphs/")
    n_values = range(0, 10, length=100)
    
    # Calculate all derivatives
    r_values = [radius_function(r0, n) for n in n_values]
    dr_values = [abs(first_derivative(r0, n)) for n in n_values]
    d2r_values = [abs(second_derivative(r0, n)) for n in n_values]
    d3r_values = [abs(third_derivative(r0, n)) for n in n_values]
    
    # Plot 1: All derivatives on log scale
    p1 = plot(n_values, r_values,
              line=(:blue, 3), label="r(n) - Position",
              xlabel="Iteration (n)", ylabel="Value (log scale)",
              title="All Derivatives (Log Scale)",
              yscale=:log10, legend=:topleft)
    plot!(p1, n_values, dr_values,
          line=(:red, 3), label="|dr/dn| - Velocity")
    plot!(p1, n_values, d2r_values,
          line=(:green, 3), label="|d²r/dn²| - Acceleration")
    plot!(p1, n_values, d3r_values,
          line=(:purple, 3), label="|d³r/dn³| - Jerk")
    
    # Plot 2: Ratio dr/r (constant!)
    ratio_values = [first_derivative(r0, n) / radius_function(r0, n) for n in n_values]
    ln_sqrt2 = log(sqrt(2))
    
    p2 = plot(n_values, ratio_values,
              line=(:blue, 3), label="(dr/dn) / r",
              xlabel="Iteration (n)", ylabel="Ratio",
              title="Derivative Ratio = ln(√2) (Constant!)",
              legend=:bottom)
    hline!(p2, [ln_sqrt2], line=(:red, 2, :dash), label="ln(√2) ≈ 0.3466")
    
    # Plot 3: Area expansion rate
    area_rate = [abs(directional_derivative_magnitude(r0, n)) for n in n_values]
    
    p3 = plot(n_values, area_rate,
              line=(:green, 3), fill=(0, 0.2, :green),
              xlabel="Iteration (n)", ylabel="dA/dn",
              title="Multidirectional Expansion: Area Growth Rate",
              label="Area Rate (all directions)", legend=:topleft)
    
    # Plot 4: Velocity field visualization
    p4 = plot(aspect_ratio=:equal, title="Radial Velocity Field",
              xlabel="x", ylabel="y", legend=false)
    
    # Draw circles at different iterations
    for n in [0, 2, 4, 6, 8]
        r = radius_function(r0, Float64(n))
        θ = range(0, 2π, length=100)
        x = r .* cos.(θ)
        y = r .* sin.(θ)
        plot!(p4, x, y, line=(:blue, 2, 0.5))
        
        # Add velocity arrows (radial)
        for angle in [0, π/4, π/2, 3π/4, π, 5π/4, 3π/2, 7π/4]
            x_pos = r * cos(angle)
            y_pos = r * sin(angle)
            dr = first_derivative(r0, Float64(n))
            dx = dr * cos(angle) * 0.5
            dy = dr * sin(angle) * 0.5
            plot!(p4, [x_pos, x_pos+dx], [y_pos, y_pos+dy],
                  arrow=true, line=(:red, 2))
        end
    end
    
    # Combine all plots
    p = plot(p1, p2, p3, p4, layout=(2, 2), size=(1400, 1000))
    
    filepath = joinpath(save_path, "derivative_analysis.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    # Run tests
    test_derivative_properties(5.0)
    
    println("\n" * "="^80)
    println("Generating derivative visualizations...")
    println("="^80)
    
    # Check if Plots is available
    try
        using Plots
        plot_derivative_analysis(5.0)
        println("\nVisualization complete!")
    catch e
        println("\nNote: Install Plots.jl to generate visualizations")
        println("Run: using Pkg; Pkg.add(\"Plots\")")
    end
end

