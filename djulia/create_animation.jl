"""
Create Animated GIF of Geometric-Quantum Scaling

Shows the dynamic scaling behavior with circles inscribed in squares,
expanding by √2 at each iteration. Visualizes the equations in motion!
"""

using Plots
using Printf

include("scaling_algorithm_inscribed_circle.jl")
include("quantum_geometric_scaling.jl")

"""
    create_scaling_animation(initial_radius, n_iterations; save_path="graphs/")

Create an animated GIF showing the scaling algorithm in action.
"""
function create_scaling_animation(initial_radius::Float64, n_iterations::Int; 
                                  save_path="graphs/", fps=2)
    println("\n" * "="^80)
    println("CREATING ANIMATED GIF: Geometric-Quantum Scaling")
    println("="^80)
    println()
    
    # Create animation
    anim = @animate for i in 0:n_iterations
        # Calculate current state
        config = scale_n_times(SquareWithInscribedCircle(initial_radius), i)
        r = config.radius
        
        # Set up plot with fixed aspect ratio
        p = plot(aspect_ratio=:equal, 
                xlabel="x", ylabel="y",
                title="Iteration $i: Radius = $(round(r, digits=2))",
                legend=:topright,
                size=(800, 800),
                xlim=(-r*1.2, r*1.2),
                ylim=(-r*1.2, r*1.2),
                grid=true,
                framestyle=:box)
        
        # Draw the square (constraint/domain)
        plot!(p, [-r, r, r, -r, -r], [-r, -r, r, r, -r],
              line=(:blue, 3), label="Domain (Square)", fillalpha=0.1, fill=(0, :blue))
        
        # Draw the inscribed circle (possible states)
        θ = range(0, 2π, length=100)
        x_circle = r .* cos.(θ)
        y_circle = r .* sin.(θ)
        plot!(p, x_circle, y_circle,
              line=(:red, 3), fill=(0, 0.2, :red),
              label="States (Circle)")
        
        # Draw the diagonal (becomes next radius)
        if i < n_iterations
            plot!(p, [0, r], [0, r],
                  line=(:green, 2, :dash),
                  arrow=true,
                  label="Diagonal = r√2")
        end
        
        # Add center point
        scatter!(p, [0], [0], marker=(:star, 10, :yellow), label="Origin")
        
        # Add text annotations
        annotate!(p, 0, -r*1.1,
                 text(@sprintf("r = %.2f\nGrowth factor: (√2)^%d = %.2f",
                              r, i, (sqrt(2))^i), 10, :bottom))
        
        p
    end
    
    filepath = joinpath(save_path, "geometric_scaling_animation.gif")
    gif(anim, filepath, fps=fps)
    println("Saved: $filepath")
    println("FPS: $fps")
    println()
    
    return filepath
end

"""
    create_velocity_field_animation(initial_radius, n_iterations; save_path="graphs/")

Create animated GIF showing velocity vectors (first derivative).
"""
function create_velocity_field_animation(initial_radius::Float64, n_iterations::Int;
                                        save_path="graphs/", fps=2)
    println("Creating velocity field animation...")
    
    anim = @animate for i in 0:n_iterations
        config = scale_n_times(SquareWithInscribedCircle(initial_radius), i)
        r = config.radius
        dr = first_derivative_at_iteration(initial_radius, i)
        
        p = plot(aspect_ratio=:equal,
                xlabel="Position", ylabel="Position",
                title="Velocity Field at Iteration $i\ndr/dn = $(round(dr, digits=2))",
                legend=false,
                size=(800, 800),
                xlim=(-r*1.3, r*1.3),
                ylim=(-r*1.3, r*1.3))
        
        # Draw circle
        θ = range(0, 2π, length=100)
        plot!(p, r .* cos.(θ), r .* sin.(θ), line=(:blue, 3))
        
        # Draw velocity vectors (radial expansion)
        n_arrows = 12
        for angle in range(0, 2π, length=n_arrows+1)[1:end-1]
            x_start = r * cos(angle)
            y_start = r * sin(angle)
            # Velocity vector
            scale_factor = 0.3
            dx = dr * cos(angle) * scale_factor
            dy = dr * sin(angle) * scale_factor
            plot!(p, [x_start, x_start+dx], [y_start, y_start+dy],
                  arrow=true, line=(:red, 3), linewidth=2)
        end
        
        annotate!(p, 0, -r*1.2,
                 text(@sprintf("Expansion velocity: %.2f units/iteration", dr), 12))
        
        p
    end
    
    filepath = joinpath(save_path, "velocity_field_animation.gif")
    gif(anim, filepath, fps=fps)
    println("Saved: $filepath")
    println()
    
    return filepath
end

"""
    create_quantum_geometric_duality_animation(initial_radius, n_iterations; save_path="graphs/")

Show geometric expansion and quantum normalization side-by-side.
"""
function create_quantum_geometric_duality_animation(initial_radius::Float64, n_iterations::Int;
                                                   save_path="graphs/", fps=2)
    println("Creating quantum-geometric duality animation...")
    
    anim = @animate for i in 0:n_iterations
        # Geometric expansion
        geom_factor = (sqrt(2))^i
        
        # Quantum normalization
        quant_factor = (1/sqrt(2))^i
        
        # Create side-by-side plots
        p1 = plot(aspect_ratio=:equal,
                 title="Geometric Expansion\n×(√2)^$i = $(round(geom_factor, digits=3))",
                 legend=false,
                 xlim=(-20, 20), ylim=(-20, 20))
        
        r_geom = initial_radius * geom_factor
        θ = range(0, 2π, length=100)
        plot!(p1, r_geom .* cos.(θ), r_geom .* sin.(θ),
              line=(:blue, 3), fill=(0, 0.3, :blue))
        scatter!(p1, [0], [0], marker=(:star, 8))
        
        p2 = plot(aspect_ratio=:equal,
                 title="Quantum Normalization\n×(1/√2)^$i = $(round(quant_factor, digits=3))",
                 legend=false,
                 xlim=(-20, 20), ylim=(-20, 20))
        
        r_quant = initial_radius / geom_factor
        plot!(p2, r_quant .* cos.(θ), r_quant .* sin.(θ),
              line=(:red, 3), fill=(0, 0.3, :red))
        scatter!(p2, [0], [0], marker=(:star, 8))
        
        # Product should equal 1
        product = geom_factor * quant_factor
        
        p3 = plot(framestyle=:none, xlim=[0,1], ylim=[0,1], legend=false)
        annotate!(p3, 0.5, 0.5,
                 text(@sprintf("Perfect Duality!\n(√2)^%d × (1/√2)^%d = %.6f ≈ 1",
                              i, i, product), 14, :center))
        
        plot(p1, p2, p3, layout=@layout[a b; c], size=(1200, 900))
    end
    
    filepath = joinpath(save_path, "quantum_geometric_duality_animation.gif")
    gif(anim, filepath, fps=fps)
    println("Saved: $filepath")
    println()
    
    return filepath
end

"""
    create_growth_comparison_animation(initial_radius, n_iterations; save_path="graphs/")

Compare different growth rates visually.
"""
function create_growth_comparison_animation(initial_radius::Float64, n_iterations::Int;
                                           save_path="graphs/", fps=2)
    println("Creating growth comparison animation...")
    
    anim = @animate for i in 0:n_iterations
        p = plot(xlabel="Iteration", ylabel="Radius",
                title="Growth Comparison: Iteration $i",
                legend=:topleft,
                size=(1000, 700),
                xlim=(0, n_iterations),
                ylim=(0, initial_radius * (sqrt(2))^n_iterations * 1.1))
        
        # Plot growth trajectories
        iterations = 0:i
        
        # Our √2 growth
        sqrt2_growth = [initial_radius * (sqrt(2))^n for n in iterations]
        plot!(p, iterations, sqrt2_growth,
              line=(:blue, 4), marker=(:circle, 6),
              label="√2 growth (ours)")
        
        # Linear growth for comparison
        linear_growth = [initial_radius * (1 + 0.4*n) for n in iterations]
        plot!(p, iterations, linear_growth,
              line=(:green, 2, :dash),
              label="Linear growth")
        
        # Quadratic growth for comparison
        quad_growth = [initial_radius * (1 + 0.1*n^2) for n in iterations]
        plot!(p, iterations, quad_growth,
              line=(:red, 2, :dash),
              label="Quadratic growth")
        
        # Add current values
        if i > 0
            annotate!(p, i, sqrt2_growth[end],
                     text(@sprintf("r=%.2f", sqrt2_growth[end]), 10, :bottom))
        end
        
        p
    end
    
    filepath = joinpath(save_path, "growth_comparison_animation.gif")
    gif(anim, filepath, fps=fps)
    println("Saved: $filepath")
    println()
    
    return filepath
end

"""
    create_all_animations(initial_radius=5.0, n_iterations=10)

Create all animated visualizations.
"""
function create_all_animations(initial_radius::Float64=5.0, n_iterations::Int=10)
    println("\n" * "="^80)
    println("GENERATING ALL ANIMATED VISUALIZATIONS")
    println("="^80)
    println()
    println("Initial radius: $initial_radius")
    println("Iterations: $n_iterations")
    println()
    
    save_path = "graphs/"
    mkpath(save_path)
    
    files = []
    
    # 1. Basic scaling animation
    push!(files, create_scaling_animation(initial_radius, n_iterations, 
                                         save_path=save_path, fps=2))
    
    # 2. Velocity field animation
    push!(files, create_velocity_field_animation(initial_radius, n_iterations,
                                                 save_path=save_path, fps=2))
    
    # 3. Quantum-geometric duality
    push!(files, create_quantum_geometric_duality_animation(initial_radius, n_iterations,
                                                           save_path=save_path, fps=1))
    
    # 4. Growth comparison
    push!(files, create_growth_comparison_animation(initial_radius, n_iterations,
                                                   save_path=save_path, fps=2))
    
    println("="^80)
    println("ALL ANIMATIONS COMPLETE!")
    println("="^80)
    println("\nCreated $(length(files)) animated GIFs:")
    for (i, file) in enumerate(files)
        println("  $i. $file")
    end
    println()
    println("Use these in:")
    println("  - Presentations")
    println("  - Papers")
    println("  - Educational materials")
    println("  - Social media")
    println("  - Conference talks")
    println()
    
    return files
end

# Helper function for first derivative calculation
function first_derivative_at_iteration(r0, n)
    return r0 * (sqrt(2))^n * log(sqrt(2))
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    println("\nGenerating animated GIFs...")
    println("This may take a minute...\n")
    
    create_all_animations(5.0, 10)
    
    println("Done! Check the graphs/ directory for your animations.")
end

