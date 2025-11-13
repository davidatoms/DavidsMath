"""
JAX Implementation of Geometric Scaling Algorithm

Uses Google's JAX for automatic differentiation and GPU acceleration.

Advantages of JAX:
- Automatic differentiation (verify derivative formulas)
- Just-In-Time compilation (fast)
- GPU/TPU support
- Compatible with NumPy
"""

import jax
import jax.numpy as jnp
from jax import grad, jit, vmap
import numpy as np
import matplotlib.pyplot as plt

# Enable 64-bit precision
jax.config.update("jax_enable_x64", True)

# ============================================================================
# CORE SCALING FUNCTIONS
# ============================================================================

@jit
def radius(n: float, r0: float = 1.0, scale: float = jnp.sqrt(2)) -> float:
    """
    Compute radius at iteration n (continuous extension).
    
    r(n) = r₀ * scale^n
    """
    return r0 * jnp.power(scale, n)

@jit
def radius_discrete(n: int, r0: float = 1.0, scale: float = jnp.sqrt(2)) -> float:
    """Discrete version for integer iterations."""
    return r0 * jnp.power(scale, n)

# Automatic differentiation!
first_derivative = jit(grad(radius, argnums=0))
second_derivative = jit(grad(first_derivative, argnums=0))
third_derivative = jit(grad(second_derivative, argnums=0))

# ============================================================================
# VERIFY DERIVATIVE FORMULAS
# ============================================================================

def verify_derivatives(r0: float = 5.0, n: float = 5.0, scale: float = jnp.sqrt(2)):
    """
    Verify that automatic differentiation matches our theoretical formulas.
    
    Theoretical:
    - dr/dn = r₀ * scale^n * ln(scale)
    - d²r/dn² = r₀ * scale^n * [ln(scale)]²
    - d³r/dn³ = r₀ * scale^n * [ln(scale)]³
    """
    print("="*80)
    print("DERIVATIVE VERIFICATION (JAX Autodiff)")
    print("="*80)
    print()
    
    # Compute using JAX autodiff
    r = radius(n, r0, scale)
    dr = first_derivative(n, r0, scale)
    d2r = second_derivative(n, r0, scale)
    d3r = third_derivative(n, r0, scale)
    
    # Theoretical values
    ln_scale = jnp.log(scale)
    r_theory = r0 * scale**n
    dr_theory = r0 * scale**n * ln_scale
    d2r_theory = r0 * scale**n * ln_scale**2
    d3r_theory = r0 * scale**n * ln_scale**3
    
    print(f"At n = {n}, r₀ = {r0}, scale = {float(scale):.6f}")
    print()
    print(f"{'Derivative':<20} {'JAX Autodiff':<20} {'Theoretical':<20} {'Match':<10}")
    print("-"*80)
    print(f"{'r(n)':<20} {float(r):<20.6f} {float(r_theory):<20.6f} {'✓' if jnp.abs(r - r_theory) < 1e-10 else '✗'}")
    print(f"{'dr/dn':<20} {float(dr):<20.6f} {float(dr_theory):<20.6f} {'✓' if jnp.abs(dr - dr_theory) < 1e-10 else '✗'}")
    print(f"{'d²r/dn²':<20} {float(d2r):<20.6f} {float(d2r_theory):<20.6f} {'✓' if jnp.abs(d2r - d2r_theory) < 1e-10 else '✗'}")
    print(f"{'d³r/dn³':<20} {float(d3r):<20.6f} {float(d3r_theory):<20.6f} {'✓' if jnp.abs(d3r - d3r_theory) < 1e-10 else '✗'}")
    print()
    
    # Verify ratios
    ratio1 = dr / r
    ratio2 = d2r / dr
    ratio3 = d3r / d2r
    
    print("Derivative Ratios:")
    print(f"  (dr/dn) / r       = {float(ratio1):.6f}")
    print(f"  (d²r/dn²) / (dr/dn) = {float(ratio2):.6f}")
    print(f"  (d³r/dn³) / (d²r/dn²) = {float(ratio3):.6f}")
    print(f"  ln(scale)           = {float(ln_scale):.6f}")
    print(f"  All equal to ln(√2)? {jnp.allclose(jnp.array([ratio1, ratio2, ratio3]), ln_scale)}")
    print()

# ============================================================================
# VECTORIZED COMPUTATIONS
# ============================================================================

@jit
def compute_derivatives_batch(n_values: jnp.ndarray, 
                               r0: float = 5.0, 
                               scale: float = jnp.sqrt(2)):
    """
    Compute all derivatives for multiple n values at once.
    Demonstrates JAX's vectorization capabilities.
    """
    # Vectorize over n
    r_vec = vmap(lambda n: radius(n, r0, scale))(n_values)
    dr_vec = vmap(lambda n: first_derivative(n, r0, scale))(n_values)
    d2r_vec = vmap(lambda n: second_derivative(n, r0, scale))(n_values)
    d3r_vec = vmap(lambda n: third_derivative(n, r0, scale))(n_values)
    
    return r_vec, dr_vec, d2r_vec, d3r_vec

# ============================================================================
# COMPLEXITY EXPLORATION
# ============================================================================

@jit
def geometric_complexity(n: float, r0: float = 1.0, scale: float = jnp.sqrt(2)) -> float:
    """State space size at iteration n."""
    return radius(n, r0, scale)

@jit
def complexity_growth_rate(n: float, r0: float = 1.0, scale: float = jnp.sqrt(2)) -> float:
    """Rate of complexity growth."""
    return first_derivative(n, r0, scale)

@jit
def characteristic_growth(scale: float) -> float:
    """ln(scale) - characterizes the complexity class?"""
    return jnp.log(scale)

def analyze_complexity_classes():
    """Analyze different scaling factors as potential complexity classes."""
    print("="*80)
    print("COMPLEXITY CLASS ANALYSIS (JAX)")
    print("="*80)
    print()
    
    scales = {
        "Sqrt-2": jnp.sqrt(2.0),
        "Golden": (1.0 + jnp.sqrt(5.0))/2.0,
        "Exponential": 2.0,
        "Natural": jnp.e,
        "Cubic": 3.0,
    }
    
    print(f"{'Class':<15} {'Scale':<15} {'ln(scale)':<15} {'Growth Rate':<15}")
    print("-"*80)
    
    n = 5.0
    r0 = 1.0
    
    for name, scale in scales.items():
        ln_s = characteristic_growth(scale)
        complexity = geometric_complexity(n, r0, scale)
        growth = complexity_growth_rate(n, r0, scale)
        
        print(f"{name:<15} {float(scale):<15.6f} {float(ln_s):<15.6f} {float(growth):<15.6f}")
    
    print()

# ============================================================================
# OPTIMIZATION: FIND OPTIMAL SCALING
# ============================================================================

def find_optimal_scale_for_target(target_ratio: float, 
                                  initial_scale: float = 2.0,
                                  learning_rate: float = 0.01,
                                  n_iterations: int = 100):
    """
    Given a target derivative ratio, find the scaling factor.
    
    Example: If we observe ln(scale) = 0.5 in nature, what is scale?
    Answer: scale = e^0.5 ≈ 1.649
    
    This demonstrates JAX's optimization capabilities.
    """
    print("="*80)
    print("OPTIMIZATION: Find Scaling Factor from Observed Growth Rate")
    print("="*80)
    print()
    
    # Loss function: |ln(scale) - target|²
    def loss(scale):
        return (jnp.log(scale) - target_ratio)**2
    
    # Gradient of loss
    grad_loss = jit(grad(loss))
    
    # Optimize
    scale = initial_scale
    print(f"Target: ln(scale) = {target_ratio}")
    print(f"Initial scale: {scale}")
    print()
    
    for i in range(n_iterations):
        g = grad_loss(scale)
        scale = scale - learning_rate * g
        
        if i % 20 == 0:
            current_loss = loss(scale)
            print(f"Iteration {i}: scale = {float(scale):.6f}, "
                  f"ln(scale) = {float(jnp.log(scale)):.6f}, "
                  f"loss = {float(current_loss):.8f}")
    
    print()
    print(f"Final scale: {float(scale):.6f}")
    print(f"Final ln(scale): {float(jnp.log(scale)):.6f}")
    print(f"Theoretical: e^{target_ratio} = {float(jnp.exp(target_ratio)):.6f}")
    print()

# ============================================================================
# VISUALIZATION
# ============================================================================

def plot_derivatives(save_path="graphs/"):
    """Plot all derivatives using JAX computations."""
    n_values = jnp.linspace(0, 10, 100)
    r0 = 5.0
    scale = jnp.sqrt(2.0)
    
    # Compute using JAX
    r, dr, d2r, d3r = compute_derivatives_batch(n_values, r0, scale)
    
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Plot 1: All derivatives
    ax = axes[0, 0]
    ax.semilogy(n_values, r, 'b-', label='r(n)', linewidth=2)
    ax.semilogy(n_values, dr, 'r-', label='dr/dn', linewidth=2)
    ax.semilogy(n_values, d2r, 'g-', label='d²r/dn²', linewidth=2)
    ax.semilogy(n_values, d3r, 'm-', label='d³r/dn³', linewidth=2)
    ax.set_xlabel('Iteration n')
    ax.set_ylabel('Value (log scale)')
    ax.set_title('All Derivatives (JAX Autodiff)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Plot 2: Derivative ratios
    ax = axes[0, 1]
    ratio1 = dr / r
    ratio2 = d2r / dr
    ratio3 = d3r / d2r
    ax.plot(n_values, ratio1, 'b-', label='(dr/dn)/r', linewidth=2)
    ax.plot(n_values, ratio2, 'r-', label='(d²r/dn²)/(dr/dn)', linewidth=2)
    ax.plot(n_values, ratio3, 'g-', label='(d³r/dn³)/(d²r/dn²)', linewidth=2)
    ax.axhline(y=float(jnp.log(scale)), color='k', linestyle='--', 
               label=f'ln(√2) = {float(jnp.log(scale)):.4f}')
    ax.set_xlabel('Iteration n')
    ax.set_ylabel('Ratio')
    ax.set_title('Derivative Ratios = ln(√2) (Constant!)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Plot 3: Complexity classes
    ax = axes[1, 0]
    scales_dict = {
        "√2": jnp.sqrt(2.0),
        "φ": (1.0 + jnp.sqrt(5.0))/2.0,
        "2": 2.0,
        "e": jnp.e,
    }
    for name, s in scales_dict.items():
        r_s = vmap(lambda n: radius(n, 1.0, s))(n_values)
        ax.semilogy(n_values, r_s, label=f'{name}', linewidth=2)
    ax.set_xlabel('Iteration n')
    ax.set_ylabel('Complexity (log scale)')
    ax.set_title('Different Complexity Classes')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Plot 4: Growth rates
    ax = axes[1, 1]
    scales_list = jnp.array([jnp.sqrt(2.0), (1+jnp.sqrt(5))/2, 2.0, jnp.e, 3.0])
    ln_scales = jnp.log(scales_list)
    names = ["√2", "φ", "2", "e", "3"]
    ax.bar(names, ln_scales, color=['blue', 'green', 'red', 'orange', 'purple'])
    ax.set_ylabel('ln(scale) - Growth Rate')
    ax.set_title('Characteristic Growth Constants')
    ax.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig(f'{save_path}/jax_derivatives_analysis.png', dpi=150)
    print(f"Saved: {save_path}/jax_derivatives_analysis.png")
    plt.close()

# ============================================================================
# MAIN
# ============================================================================

def main():
    print("\n")
    print("╔" + "="*78 + "╗")
    print("║" + " "*25 + "JAX GEOMETRIC SCALING" + " "*32 + "║")
    print("╚" + "="*78 + "╝")
    print("\n")
    
    print(f"JAX version: {jax.__version__}")
    print(f"Device: {jax.devices()}")
    print()
    
    # 1. Verify derivatives
    verify_derivatives()
    
    # 2. Complexity analysis
    analyze_complexity_classes()
    
    # 3. Optimization example
    find_optimal_scale_for_target(target_ratio=float(jnp.log(jnp.sqrt(2))))
    
    # 4. Visualization
    plot_derivatives()
    
    print("\n")
    print("="*80)
    print("JAX ADVANTAGES")
    print("="*80)
    print()
    print("✓ Automatic differentiation (no manual derivatives needed)")
    print("✓ GPU/TPU support (for large-scale simulations)")
    print("✓ JIT compilation (fast execution)")
    print("✓ Vectorization (batch computations)")
    print("✓ Integration with ML frameworks")
    print()
    print("NEXT: Can use JAX for:")
    print("- Crystal structure optimization")
    print("- Black hole metric calculations")
    print("- Large-scale complexity simulations")
    print("- Neural network models of geometric patterns")
    print()

if __name__ == "__main__":
    main()

