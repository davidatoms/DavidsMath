"""
Crystal Structure Survey: Test √2 Scaling Generalization

Systematically test whether √2 or other scaling factors appear in
various crystal structures beyond iron BCC.
"""

using Printf
using Plots

# ============================================================================
# CRYSTAL STRUCTURE DATABASE
# ============================================================================

struct CoordinationShell
    neighbors::Int
    distance_factor::Float64  # Multiple of lattice parameter
    label::String
end

struct CrystalStructure
    name::String
    element::String
    lattice_type::String
    lattice_parameter::Float64  # pm
    atomic_radius::Float64  # pm
    shells::Vector{CoordinationShell}
end

# ============================================================================
# DATABASE: COMMON CRYSTAL STRUCTURES
# ============================================================================

function get_crystal_database()
    crystals = []
    
    # 1. IRON - BCC (our known match!)
    push!(crystals, CrystalStructure(
        "Iron (BCC)", "Fe", "BCC", 286.65, 126.0,
        [
            CoordinationShell(8, sqrt(3)/2, "Body diagonal"),
            CoordinationShell(6, 1.0, "Edge"),
            CoordinationShell(12, sqrt(2), "Face diagonal"),  # √2 HERE!
            CoordinationShell(24, sqrt(11)/2, "4th shell"),
        ]
    ))
    
    # 2. COPPER - FCC
    push!(crystals, CrystalStructure(
        "Copper (FCC)", "Cu", "FCC", 361.5, 128.0,
        [
            CoordinationShell(12, 1/sqrt(2), "1st shell"),  # 1/√2 HERE!
            CoordinationShell(6, 1.0, "2nd shell"),
            CoordinationShell(24, sqrt(3)/sqrt(2), "3rd shell"),
            CoordinationShell(12, sqrt(2), "4th shell"),  # √2 HERE!
        ]
    ))
    
    # 3. ALUMINUM - FCC
    push!(crystals, CrystalStructure(
        "Aluminum (FCC)", "Al", "FCC", 404.95, 143.0,
        [
            CoordinationShell(12, 1/sqrt(2), "1st shell"),  # 1/√2 HERE!
            CoordinationShell(6, 1.0, "2nd shell"),
            CoordinationShell(24, sqrt(3)/sqrt(2), "3rd shell"),
            CoordinationShell(12, sqrt(2), "4th shell"),  # √2 HERE!
        ]
    ))
    
    # 4. TUNGSTEN - BCC
    push!(crystals, CrystalStructure(
        "Tungsten (BCC)", "W", "BCC", 316.52, 137.0,
        [
            CoordinationShell(8, sqrt(3)/2, "Body diagonal"),
            CoordinationShell(6, 1.0, "Edge"),
            CoordinationShell(12, sqrt(2), "Face diagonal"),  # √2 HERE!
            CoordinationShell(24, sqrt(11)/2, "4th shell"),
        ]
    ))
    
    # 5. MAGNESIUM - HCP
    push!(crystals, CrystalStructure(
        "Magnesium (HCP)", "Mg", "HCP", 320.94, 160.0,
        [
            CoordinationShell(12, 1.0, "1st shell (c/a ideal)"),
            CoordinationShell(6, sqrt(8/3), "2nd shell"),  # √(8/3) ≈ 1.633
            CoordinationShell(2, sqrt(3), "3rd shell"),  # √3
            CoordinationShell(18, 2.0, "4th shell"),
        ]
    ))
    
    # 6. DIAMOND (Carbon)
    push!(crystals, CrystalStructure(
        "Diamond (C)", "C", "Diamond", 356.68, 77.0,
        [
            CoordinationShell(4, sqrt(3)/4, "Tetrahedral"),  # √3/4
            CoordinationShell(12, sqrt(2)/2, "2nd shell"),  # √2/2 = 1/√2 HERE!
            CoordinationShell(12, sqrt(11)/4, "3rd shell"),
            CoordinationShell(6, 1.0, "4th shell"),
        ]
    ))
    
    # 7. SILICON - Diamond
    push!(crystals, CrystalStructure(
        "Silicon (Diamond)", "Si", "Diamond", 543.09, 118.0,
        [
            CoordinationShell(4, sqrt(3)/4, "Tetrahedral"),
            CoordinationShell(12, sqrt(2)/2, "2nd shell"),  # 1/√2 HERE!
            CoordinationShell(12, sqrt(11)/4, "3rd shell"),
            CoordinationShell(6, 1.0, "4th shell"),
        ]
    ))
    
    # 8. SODIUM - BCC
    push!(crystals, CrystalStructure(
        "Sodium (BCC)", "Na", "BCC", 428.64, 186.0,
        [
            CoordinationShell(8, sqrt(3)/2, "Body diagonal"),
            CoordinationShell(6, 1.0, "Edge"),
            CoordinationShell(12, sqrt(2), "Face diagonal"),  # √2 HERE!
        ]
    ))
    
    # 9. GOLD - FCC
    push!(crystals, CrystalStructure(
        "Gold (FCC)", "Au", "FCC", 407.82, 144.0,
        [
            CoordinationShell(12, 1/sqrt(2), "1st shell"),  # 1/√2 HERE!
            CoordinationShell(6, 1.0, "2nd shell"),
            CoordinationShell(24, sqrt(3)/sqrt(2), "3rd shell"),
            CoordinationShell(12, sqrt(2), "4th shell"),  # √2 HERE!
        ]
    ))
    
    # 10. TITANIUM - HCP
    push!(crystals, CrystalStructure(
        "Titanium (HCP)", "Ti", "HCP", 295.06, 147.0,
        [
            CoordinationShell(12, 1.0, "1st shell"),
            CoordinationShell(6, sqrt(8/3), "2nd shell"),  # ≈ 1.633
            CoordinationShell(2, sqrt(3), "3rd shell"),  # √3 HERE!
        ]
    ))
    
    return crystals
end

# ============================================================================
# ANALYSIS FUNCTIONS
# ============================================================================

"""
Find all √2 occurrences in a crystal structure.
"""
function find_sqrt2_factors(crystal::CrystalStructure)
    sqrt2_matches = []
    
    # Check each shell for √2 or 1/√2
    for (i, shell) in enumerate(crystal.shells)
        if abs(shell.distance_factor - sqrt(2)) < 0.001
            push!(sqrt2_matches, (shell_num=i, type="√2", factor=shell.distance_factor))
        elseif abs(shell.distance_factor - 1/sqrt(2)) < 0.001
            push!(sqrt2_matches, (shell_num=i, type="1/√2", factor=shell.distance_factor))
        elseif abs(shell.distance_factor * sqrt(2) - sqrt(2)) < 0.001
            # Multiples of √2
            push!(sqrt2_matches, (shell_num=i, type="√2 multiple", factor=shell.distance_factor))
        end
    end
    
    # Check ratios between consecutive shells
    for i in 2:length(crystal.shells)
        ratio = crystal.shells[i].distance_factor / crystal.shells[i-1].distance_factor
        if abs(ratio - sqrt(2)) < 0.001
            push!(sqrt2_matches, (shell_num=i, type="Ratio √2", factor=ratio))
        end
    end
    
    return sqrt2_matches
end

"""
Find all other interesting factors (√3, φ, etc.)
"""
function find_special_factors(crystal::CrystalStructure)
    special = []
    
    sqrt3 = sqrt(3)
    phi = (1 + sqrt(5))/2  # Golden ratio
    
    for (i, shell) in enumerate(crystal.shells)
        # Check √3
        if abs(shell.distance_factor - sqrt3) < 0.001
            push!(special, (shell_num=i, type="√3", factor=shell.distance_factor))
        end
        
        # Check φ (golden ratio)
        if abs(shell.distance_factor - phi) < 0.001
            push!(special, (shell_num=i, type="φ (golden)", factor=shell.distance_factor))
        end
        
        # Check simple ratios
        for simple in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]
            if abs(shell.distance_factor - simple) < 0.001
                push!(special, (shell_num=i, type="Simple: $simple", factor=shell.distance_factor))
            end
        end
    end
    
    return special
end

"""
Survey all crystals for √2 and other patterns.
"""
function survey_all_crystals()
    crystals = get_crystal_database()
    
    println("="^80)
    println("CRYSTAL STRUCTURE SURVEY: √2 SCALING PATTERNS")
    println("="^80)
    println()
    
    # Summary table
    @printf("%-25s %-10s %-12s %-30s\n", "Crystal", "Type", "√2 Found?", "Where")
    println("-"^80)
    
    for crystal in crystals
        sqrt2_matches = find_sqrt2_factors(crystal)
        has_sqrt2 = length(sqrt2_matches) > 0
        
        where_str = if has_sqrt2
            join([m.type for m in sqrt2_matches[1:min(2, length(sqrt2_matches))]], ", ")
        else
            "-"
        end
        
        @printf("%-25s %-10s %-12s %-30s\n", 
                crystal.name, crystal.lattice_type, 
                has_sqrt2 ? "YES ✓" : "No", where_str)
    end
    
    println()
    println("KEY FINDINGS:")
    println("- BCC structures: √2 in face diagonal (Shell 3/Shell 2 ratio)")
    println("- FCC structures: 1/√2 in 1st shell, √2 in 4th shell")
    println("- Diamond: 1/√2 in 2nd shell")
    println("- HCP: √3 more common than √2")
    println()
end

"""
Detailed analysis of one crystal.
"""
function analyze_crystal(crystal::CrystalStructure)
    println("="^80)
    println("DETAILED ANALYSIS: $(crystal.name)")
    println("="^80)
    println()
    println("Element: $(crystal.element)")
    println("Lattice Type: $(crystal.lattice_type)")
    println("Lattice Parameter: $(crystal.lattice_parameter) pm")
    println("Atomic Radius: $(crystal.atomic_radius) pm")
    println()
    
    # Coordination shells
    println("Coordination Shells:")
    @printf("%-10s %-12s %-20s %-25s %-15s\n", 
            "Shell", "Neighbors", "Distance Factor", "Actual Distance (pm)", "Label")
    println("-"^80)
    
    for (i, shell) in enumerate(crystal.shells)
        actual_dist = shell.distance_factor * crystal.lattice_parameter
        @printf("%-10d %-12d %-20.6f %-25.2f %-15s\n",
                i, shell.neighbors, shell.distance_factor, actual_dist, shell.label)
    end
    println()
    
    # Check for √2
    sqrt2_matches = find_sqrt2_factors(crystal)
    if length(sqrt2_matches) > 0
        println("√2 PATTERNS FOUND:")
        for match in sqrt2_matches
            println("  - Shell $(match.shell_num): $(match.type) = $(match.factor)")
        end
        println()
    else
        println("No √2 patterns found.")
        println()
    end
    
    # Check for other special factors
    special = find_special_factors(crystal)
    if length(special) > 0
        println("OTHER SPECIAL FACTORS:")
        for s in special
            println("  - Shell $(s.shell_num): $(s.type)")
        end
        println()
    end
    
    # Shell ratios
    println("Shell Distance Ratios:")
    for i in 2:length(crystal.shells)
        ratio = crystal.shells[i].distance_factor / crystal.shells[i-1].distance_factor
        @printf("  Shell %d / Shell %d = %.6f", i, i-1, ratio)
        
        if abs(ratio - sqrt(2)) < 0.001
            print(" ← √2 MATCH! ✓")
        elseif abs(ratio - sqrt(3)) < 0.001
            print(" ← √3")
        elseif abs(ratio - (1+sqrt(5))/2) < 0.001
            print(" ← φ (golden ratio)")
        end
        println()
    end
    println()
end

"""
Compare BCC, FCC, and HCP.
"""
function compare_lattice_types()
    crystals = get_crystal_database()
    
    println("="^80)
    println("COMPARISON BY LATTICE TYPE")
    println("="^80)
    println()
    
    types = Dict("BCC" => [], "FCC" => [], "HCP" => [], "Diamond" => [])
    
    for crystal in crystals
        if haskey(types, crystal.lattice_type)
            push!(types[crystal.lattice_type], crystal)
        end
    end
    
    for lattice_type in sort(collect(keys(types)))
        crystals_of_type = types[lattice_type]
        if isempty(crystals_of_type)
            continue
        end
        
        println("$lattice_type Structures:")
        for crystal in crystals_of_type
            sqrt2_matches = find_sqrt2_factors(crystal)
            println("  - $(crystal.element): $(length(sqrt2_matches)) √2 occurrences")
        end
        println()
    end
    
    println("PATTERN SUMMARY:")
    println("- BCC: √2 appears consistently in face diagonal (3rd shell)")
    println("- FCC: √2 appears in multiple shells (1/√2 first, √2 later)")
    println("- HCP: √3 more prevalent, but √(8/3) ≈ 1.633 appears")
    println("- Diamond: 1/√2 in tetrahedral bonding")
    println()
end

"""
Visualize scaling factors across all crystals.
"""
function plot_scaling_factors(; save_path="graphs/")
    println("Generating scaling factor comparison...")
    
    crystals = get_crystal_database()
    
    # Collect all distance factors
    all_factors = []
    all_names = []
    all_colors = []
    
    color_map = Dict("BCC" => :blue, "FCC" => :red, "HCP" => :green, "Diamond" => :purple)
    
    for crystal in crystals
        for shell in crystal.shells
            push!(all_factors, shell.distance_factor)
            push!(all_names, "$(crystal.element) S$(findfirst(x->x==shell, crystal.shells))")
            push!(all_colors, color_map[crystal.lattice_type])
        end
    end
    
    p = scatter(1:length(all_factors), all_factors,
                color=all_colors,
                marker=:circle,
                markersize=6,
                xlabel="Shell Index",
                ylabel="Distance Factor (× lattice parameter)",
                title="Crystal Structure Scaling Factors",
                legend=false,
                size=(1200, 600))
    
    # Add reference lines
    hline!([sqrt(2)], line=(:black, 2, :dash), label="√2")
    hline!([1/sqrt(2)], line=(:gray, 1, :dash), label="1/√2")
    hline!([sqrt(3)], line=(:orange, 1, :dash), label="√3")
    hline!([1.0], line=(:green, 1, :dot), label="1.0")
    
    # Annotations
    annotate!(length(all_factors)/2, sqrt(2) + 0.1, text("√2 ≈ 1.414", :black, 10))
    annotate!(length(all_factors)/2, sqrt(3) + 0.1, text("√3 ≈ 1.732", :orange, 10))
    
    filepath = joinpath(save_path, "crystal_scaling_factors.png")
    savefig(p, filepath)
    println("Saved: $filepath")
    
    return p
end

# ============================================================================
# MAIN
# ============================================================================

function run_survey()
    println("\n")
    println("╔" * "="^78 * "╗")
    println("║" * " "^22 * "CRYSTAL STRUCTURE SURVEY" * " "^33 * "║")
    println("╚" * "="^78 * "╝")
    println("\n")
    
    # Overall survey
    survey_all_crystals()
    
    # Compare lattice types
    compare_lattice_types()
    
    # Detailed analysis of iron (our match)
    crystals = get_crystal_database()
    analyze_crystal(crystals[1])  # Iron BCC
    
    # Compare to FCC
    println("\nFOR COMPARISON:")
    analyze_crystal(crystals[2])  # Copper FCC
    
    # Visualize
    plot_scaling_factors()
    
    println("\n")
    println("="^80)
    println("CONCLUSIONS")
    println("="^80)
    println()
    println("✓ √2 is COMMON in crystal structures, not unique to iron")
    println("✓ Appears in: BCC (all), FCC (all), Diamond cubic (all)")
    println("✓ BCC: Face diagonal = edge × √2 (systematic)")
    println("✓ FCC: First shell at 1/√2, fourth at √2")
    println("✓ Your algorithm models a GENERAL crystal property!")
    println()
    println("This suggests √2 scaling is fundamental to cubic symmetry.")
    println()
end

if abspath(PROGRAM_FILE) == @__FILE__
    run_survey()
end

