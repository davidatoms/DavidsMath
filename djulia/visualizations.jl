"""
Visualization Module for Geometric-Quantum Scaling

Creates beautiful visualizations of the scaling algorithm and its
connections to quantum mechanics.

Requires: Plots.jl
Install with: using Pkg; Pkg.add("Plots")
"""

using Plots
using Printf

# Include the main algorithm files
include("scaling_algorithm_inscribed_circle.jl")
include("quantum_geometric_scaling.jl")

# Set default plot settings
default(size=(1200, 800), dpi=300, fontfamily="Computer Modern")

"""
    plot_geometric_scaling_sequence(initial_radius::Float64, n_iterations::Int; save_path="graphs/")

Visualize the geometric scaling sequence showing circles inscribed in squares.
"""
function plot_geometric_scaling_sequence(initial_radius::Float64, n_iterations::Int; 
                                         save_path="graphs/")
    # Create figure with subplots
    plots_per_row = 4
    n_plots = min(n_iterations + 1, 12)  # Show first 12 iterations
    n_rows = ceil(Int, n_plots / plots_per_row)
    
    p = plot(layout=(n_rows, plots_per_row), size=(1600, 400*n_rows))
    
    config = SquareWithInscribedCircle(initial_radius)
    
    for i in 0:(n_plots-1)
        subplot_idx = i + 1
        
        # Draw square
        square_half = config.radius
        plot!(p[subplot_idx], 
              [-square_half, square_half, square_half, -square_half, -square_half],
              [-square_half, -square_half, square_half, square_half, -square_half],
              line=(:blue, 2), label="Domain (Square)",
              aspect_ratio=:equal, legend=false)
        
        # Draw inscribed circle
        θ = range(0, 2π, length=100)
        x_circle = config.radius .* cos.(θ)
        y_circle = config.radius .* sin.(θ)
        plot!(p[subplot_idx], x_circle, y_circle, 
              line=(:red, 2), fill=(0, 0.2, :red),
              label="States (Circle)")
        
        # Draw diagonal (which becomes next radius)
        plot!(p[subplot_idx], [0, config.radius], [0, config.radius],
              line=(:green, 2, :dash), label="Diagonal = r√2")
        
        # Add title with iteration info
        title!(p[subplot_idx], 
               @sprintf("n=%d\nr=%.2f", i, config.radius),
               titlefontsize=10)
        
        # Scale for next iteration
        if i < n_plots - 1
            config = scale_once(config)
        end
    end
    
    # Overall title
    plot!(p, plot_title="Geometric Scaling: Circle in Square (×√2 per iteration)",
          plot_titlefontsize=16)
    
    # Save
    filepath = joinpath(save_path, "geometric_scaling_sequence.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

"""
    plot_radius_growth(initial_radius::Float64, n_iterations::Int; save_path="graphs/")

Plot how the radius grows over iterations.
"""
function plot_radius_growth(initial_radius::Float64, n_iterations::Int; 
                           save_path="graphs/")
    iterations = 0:n_iterations
    radii = [scale_n_times_formula(initial_radius, n) for n in iterations]
    
    # Create plots
    p1 = plot(iterations, radii,
              line=(:blue, 3), marker=(:circle, 6),
              xlabel="Iteration (n)", ylabel="Radius",
              title="Radius Growth: r = r₀ × (√2)ⁿ",
              label="Radius", legend=:topleft,
              grid=true, minorgrid=true)
    
    # Add theoretical curve
    plot!(p1, iterations, radii,
          line=(:red, 2, :dash),
          label="Theory: r₀(√2)ⁿ")
    
    # Log scale version
    p2 = plot(iterations, radii,
              line=(:blue, 3), marker=(:circle, 6),
              xlabel="Iteration (n)", ylabel="Radius (log scale)",
              title="Radius Growth (Log Scale)",
              label="Radius", legend=:topleft,
              yscale=:log10,
              grid=true, minorgrid=true)
    
    # Combine plots
    p = plot(p1, p2, layout=(1, 2), size=(1400, 600))
    
    filepath = joinpath(save_path, "radius_growth.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

"""
    plot_area_expansion(initial_radius::Float64, n_iterations::Int; save_path="graphs/")

Visualize how the area of possibilities expands.
"""
function plot_area_expansion(initial_radius::Float64, n_iterations::Int;
                            save_path="graphs/")
    iterations = 0:n_iterations
    
    # Calculate areas
    circle_areas = [π * scale_n_times_formula(initial_radius, n)^2 for n in iterations]
    square_areas = [(2 * scale_n_times_formula(initial_radius, n))^2 for n in iterations]
    efficiency = circle_areas ./ square_areas
    
    # Plot 1: Areas over time
    p1 = plot(iterations, circle_areas,
              line=(:red, 3), marker=(:circle, 6),
              xlabel="Iteration (n)", ylabel="Area",
              title="Possibility Space vs Constraint",
              label="Circle (States)", legend=:topleft,
              yscale=:log10)
    
    plot!(p1, iterations, square_areas,
          line=(:blue, 3), marker=(:square, 6),
          label="Square (Domain)")
    
    # Plot 2: Efficiency (always π/4)
    p2 = plot(iterations, efficiency,
              line=(:green, 3), marker=(:diamond, 6),
              xlabel="Iteration (n)", ylabel="Efficiency",
              title="Packing Efficiency = π/4 (Invariant!)",
              label="Circle/Square Ratio", legend=:bottomright,
              ylim=[0.78, 0.79])
    
    hline!(p2, [π/4], line=(:black, 2, :dash), label="π/4 ≈ 0.7854")
    
    p = plot(p1, p2, layout=(1, 2), size=(1400, 600))
    
    filepath = joinpath(save_path, "area_expansion.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

"""
    plot_quantum_connection(initial_radius::Float64, n_iterations::Int; save_path="graphs/")

Visualize the connection to quantum mechanics.
"""
function plot_quantum_connection(initial_radius::Float64, n_iterations::Int;
                                save_path="graphs/")
    iterations = 0:n_iterations
    
    # Scaling factor
    scaling_factors = [sqrt(2)^n for n in iterations]
    
    # Quantum normalization (inverse)
    quantum_norm = [1/sqrt(2)^n for n in iterations]
    
    # Plot
    p1 = plot(iterations, scaling_factors,
              line=(:blue, 3), marker=(:circle, 6),
              xlabel="Quantum Level (n)", ylabel="Scaling Factor",
              title="Geometric Scaling: (√2)ⁿ",
              label="Geometric: (√2)ⁿ", legend=:topleft,
              yscale=:log10)
    
    p2 = plot(iterations, quantum_norm,
              line=(:red, 3), marker=(:star, 6),
              xlabel="Quantum Level (n)", ylabel="Normalization",
              title="Quantum Normalization: (1/√2)ⁿ",
              label="Quantum: (1/√2)ⁿ", legend=:topright,
              yscale=:log10)
    
    # Show they're inverses
    p3 = plot(iterations, scaling_factors .* quantum_norm,
              line=(:green, 3), marker=(:diamond, 6),
              xlabel="Level (n)", ylabel="Product",
              title="Product = 1 (Perfect Duality!)",
              label="(√2)ⁿ × (1/√2)ⁿ = 1", legend=:bottom,
              ylim=[0.9, 1.1])
    
    hline!(p3, [1.0], line=(:black, 2, :dash), label="Unity")
    
    # Create a text-only subplot for explanation
    p4 = plot(framestyle=:none, xlim=[0,1], ylim=[0,1])
    annotate!(p4, 
              [(0.5, 0.5, 
                text("Geometric Expansion ↔ Quantum Normalization\nDuality Relationship\n\n" *
                     "(√2)ⁿ × (1/√2)ⁿ = 1\n\n" *
                     "Perfect inverse relationship!", 
                     :center, 12))])
    
    p = plot(p1, p2, p3, p4, layout=(2, 2), size=(1400, 1000))
    
    filepath = joinpath(save_path, "quantum_connection.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

"""
    plot_phase_space_interpretation(initial_radius::Float64; save_path="graphs/")

Create a beautiful phase-space style visualization.
"""
function plot_phase_space_interpretation(initial_radius::Float64; save_path="graphs/")
    # Create multiple nested circles and squares
    p = plot(aspect_ratio=:equal, 
             xlabel="Position (x)", ylabel="Momentum (p)",
             title="Phase Space Interpretation: Nested State Spaces",
             legend=:topright, size=(1000, 1000))
    
    colors = [:blue, :red, :green, :purple, :orange, :brown]
    config = SquareWithInscribedCircle(initial_radius)
    
    for i in 0:5
        # Draw square (constraint)
        r = config.radius
        plot!(p, [-r, r, r, -r, -r], [-r, -r, r, r, -r],
              line=(colors[i+1], 2, 0.5), 
              label=i==0 ? "Constraints" : "",
              fillalpha=0.05)
        
        # Draw circle (states)
        θ = range(0, 2π, length=100)
        x = r .* cos.(θ)
        y = r .* sin.(θ)
        plot!(p, x, y, 
              line=(colors[i+1], 2),
              label=i==0 ? "State Spaces" : "",
              fillalpha=0.1)
        
        config = scale_once(config)
    end
    
    # Add center point
    scatter!(p, [0], [0], marker=(:star, 12, :black), label="Origin")
    
    # Add annotations
    annotate!(p, [(0, -initial_radius*30, 
                   text("Each level: ×√2 expansion\nAnalogous to quantum energy levels", 
                        :center, 12))])
    
    filepath = joinpath(save_path, "phase_space_nested.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

"""
    plot_domain_to_states_relationship(; save_path="graphs/")

Visualize the key insight: Domain → Possible States
"""
function plot_domain_to_states_relationship(; save_path="graphs/")
    domain_sizes = range(1, 50, length=100)
    state_radii = domain_sizes ./ 2
    state_areas = π .* state_radii.^2
    
    p1 = plot(domain_sizes, state_radii,
              line=(:blue, 3),
              xlabel="Domain Size (Square Side)", 
              ylabel="Max State Radius",
              title="Domain → State Space Relationship",
              label="r = domain/2", legend=:topleft,
              grid=true)
    
    p2 = plot(domain_sizes, state_areas,
              line=(:red, 3),
              xlabel="Domain Size (Square Side)",
              ylabel="Possibility Area",
              title="Domain → Total Possibilities",
              label="Area = π(domain/2)²", legend=:topleft,
              grid=true)
    
    # Inverse relationship
    state_radii_inv = range(1, 25, length=100)
    domains_needed = 2 .* state_radii_inv
    
    p3 = plot(state_radii_inv, domains_needed,
              line=(:green, 3),
              xlabel="Required State Radius",
              ylabel="Minimum Domain Needed",
              title="State Space → Required Domain\n(Inverse Problem)",
              label="domain = 2r", legend=:topleft,
              grid=true)
    
    # Create explanation subplot
    p4 = plot(framestyle=:none, xlim=[0,1], ylim=[0,1])
    annotate!(p4, 
              [(0.5, 0.5, 
                text("Given constraints (domain),\nwe can determine all possible states\n\n" *
                     "This is analogous to:\n" *
                     "Boundary conditions → Wavefunctions\n" *
                     "Configuration space → Phase space", 
                     :center, 12))])
    
    p = plot(p1, p2, p3, p4, layout=(2, 2), size=(1400, 1000))
    
    filepath = joinpath(save_path, "domain_states_relationship.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

"""
    create_all_visualizations(initial_radius::Float64=5.0, n_iterations::Int=15)

Generate all visualizations at once.
"""
function create_all_visualizations(initial_radius::Float64=5.0, n_iterations::Int=15)
    println("\n" * "="^80)
    println("GENERATING ALL VISUALIZATIONS")
    println("="^80)
    println()
    
    save_path = "graphs/"
    mkpath(save_path)  # Ensure directory exists
    
    println("1. Geometric scaling sequence...")
    plot_geometric_scaling_sequence(initial_radius, min(n_iterations, 11), save_path=save_path)
    
    println("2. Radius growth...")
    plot_radius_growth(initial_radius, n_iterations, save_path=save_path)
    
    println("3. Area expansion and efficiency...")
    plot_area_expansion(initial_radius, n_iterations, save_path=save_path)
    
    println("4. Quantum connection...")
    plot_quantum_connection(initial_radius, n_iterations, save_path=save_path)
    
    println("5. Phase space interpretation...")
    plot_phase_space_interpretation(initial_radius, save_path=save_path)
    
    println("6. Domain-states relationship...")
    plot_domain_to_states_relationship(save_path=save_path)
    
    println()
    println("="^80)
    println("ALL VISUALIZATIONS COMPLETE!")
    println("Check the graphs/ directory for output files.")
    println("="^80)
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    println("\nInstalling/Loading Plots.jl...")
    println("(This may take a moment on first run)\n")
    
    create_all_visualizations(5.0, 15)
end

