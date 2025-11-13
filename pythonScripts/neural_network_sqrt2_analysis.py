"""
Neural Network Architecture Analysis: √2 Patterns

Check if successful neural networks naturally exhibit √2 scaling
in their layer dimensions, depth-width ratios, etc.

This could revolutionize architecture search!
"""

import numpy as np
from typing import List, Tuple, Dict
import math

# ============================================================================
# FAMOUS ARCHITECTURES
# ============================================================================

ARCHITECTURES = {
    "AlexNet": [
        ("conv1", 11*11*3, 96),
        ("conv2", 5*5*96, 256),
        ("conv3", 3*3*256, 384),
        ("conv4", 3*3*384, 384),
        ("conv5", 3*3*384, 256),
        ("fc6", 256*6*6, 4096),
        ("fc7", 4096, 4096),
        ("fc8", 4096, 1000),
    ],
    
    "VGG-16": [
        ("conv1_1", 3*3*3, 64),
        ("conv1_2", 3*3*64, 64),
        ("conv2_1", 3*3*64, 128),
        ("conv2_2", 3*3*128, 128),
        ("conv3_1", 3*3*128, 256),
        ("conv3_2", 3*3*256, 256),
        ("conv3_3", 3*3*256, 256),
        ("conv4_1", 3*3*256, 512),
        ("conv4_2", 3*3*512, 512),
        ("conv4_3", 3*3*512, 512),
        ("conv5_1", 3*3*512, 512),
        ("conv5_2", 3*3*512, 512),
        ("conv5_3", 3*3*512, 512),
        ("fc6", 512*7*7, 4096),
        ("fc7", 4096, 4096),
        ("fc8", 4096, 1000),
    ],
    
    "ResNet-50": [
        ("conv1", 7*7*3, 64),
        ("layer1", 64, 256),
        ("layer2", 256, 512),
        ("layer3", 512, 1024),
        ("layer4", 1024, 2048),
        ("fc", 2048, 1000),
    ],
    
    "Transformer-Base": [
        ("embedding", 512, 512),
        ("attention_1", 512, 512),
        ("ffn_1", 512, 2048),
        ("attention_2", 2048, 512),
        ("output", 512, 512),
    ],
    
    "GPT-2-Small": [
        ("embedding", 50257, 768),
        ("layer1", 768, 3072),
        ("layer2", 3072, 768),
        ("layer3", 768, 3072),
        ("layer4", 3072, 768),
        ("output", 768, 50257),
    ],
}

# ============================================================================
# ANALYSIS FUNCTIONS
# ============================================================================

def check_sqrt2_ratio(value1: float, value2: float, tolerance: float = 0.1) -> bool:
    """Check if ratio is close to √2 or 1/√2"""
    sqrt2 = np.sqrt(2)
    ratio = value1 / value2 if value2 != 0 else 0
    
    # Check both √2 and 1/√2
    error_sqrt2 = abs(ratio - sqrt2)
    error_inv_sqrt2 = abs(ratio - 1/sqrt2)
    
    return min(error_sqrt2, error_inv_sqrt2) < tolerance

def analyze_architecture(name: str, layers: List[Tuple[str, int, int]]):
    """Analyze a single architecture for √2 patterns"""
    print(f"\n{'='*80}")
    print(f"ARCHITECTURE: {name}")
    print(f"{'='*80}\n")
    
    sqrt2 = np.sqrt(2)
    sqrt2_matches = []
    
    print(f"{'Layer':<20} {'Input':<10} {'Output':<10} {'Ratio':<10} {'√2 Match?':<15}")
    print("-" * 80)
    
    for layer_name, input_dim, output_dim in layers:
        ratio = output_dim / input_dim if input_dim > 0 else 0
        
        # Check for √2
        error_sqrt2 = abs(ratio - sqrt2)
        error_inv_sqrt2 = abs(ratio - 1/sqrt2)
        min_error = min(error_sqrt2, error_inv_sqrt2)
        
        is_sqrt2 = min_error < 0.15
        match_str = ""
        if is_sqrt2:
            if error_sqrt2 < error_inv_sqrt2:
                match_str = f"✓ ×√2 (err:{min_error:.3f})"
                sqrt2_matches.append((layer_name, ratio, "×√2", min_error))
            else:
                match_str = f"✓ ×(1/√2) (err:{min_error:.3f})"
                sqrt2_matches.append((layer_name, ratio, "×(1/√2)", min_error))
        
        print(f"{layer_name:<20} {input_dim:<10} {output_dim:<10} {ratio:<10.4f} {match_str:<15}")
    
    # Summary
    print(f"\n√2 MATCHES: {len(sqrt2_matches)}/{len(layers)} layers ({100*len(sqrt2_matches)/len(layers):.1f}%)")
    
    if sqrt2_matches:
        print("\nDetailed matches:")
        for layer, ratio, match_type, error in sqrt2_matches:
            print(f"  - {layer}: ratio={ratio:.4f} {match_type} (error: {error:.4f})")
    
    # Check consecutive layer ratios
    print("\n\nCONSECUTIVE LAYER DIMENSION RATIOS:")
    print(f"{'Layers':<30} {'Ratio':<10} {'√2 Pattern?':<15}")
    print("-" * 80)
    
    consecutive_sqrt2 = 0
    for i in range(len(layers) - 1):
        dim1 = layers[i][2]  # output of layer i
        dim2 = layers[i+1][2]  # output of layer i+1
        
        if dim1 > 0:
            ratio = dim2 / dim1
            error_sqrt2 = abs(ratio - sqrt2)
            error_inv_sqrt2 = abs(ratio - 1/sqrt2)
            min_error = min(error_sqrt2, error_inv_sqrt2)
            
            is_sqrt2 = min_error < 0.15
            match_str = ""
            if is_sqrt2:
                consecutive_sqrt2 += 1
                if error_sqrt2 < error_inv_sqrt2:
                    match_str = f"✓ ×√2 (err:{min_error:.3f})"
                else:
                    match_str = f"✓ ×(1/√2) (err:{min_error:.3f})"
            
            layer_pair = f"{layers[i][0]} → {layers[i+1][0]}"
            print(f"{layer_pair:<30} {ratio:<10.4f} {match_str:<15}")
    
    print(f"\n√2 consecutive matches: {consecutive_sqrt2}/{len(layers)-1} transitions")
    
    return len(sqrt2_matches), consecutive_sqrt2

def check_power_of_sqrt2_sequence(dims: List[int]) -> Dict:
    """
    Check if dimension sequence follows (√2)^n pattern.
    
    Example: 64, 128, 256, 512 would be perfect powers of 2
    Check: 64, 90.5, 128, 181, 256 would be powers of √2
    """
    print("\n\nPOWER SERIES ANALYSIS:")
    print("Checking if dimensions follow (√2)^n or 2^n pattern...")
    print()
    
    sqrt2 = np.sqrt(2)
    
    # Test starting from first dimension
    start_dim = dims[0]
    
    print(f"{'n':<5} {'Expected (√2)^n':<20} {'Expected 2^n':<15} {'Actual':<10} {'Best Match':<15}")
    print("-" * 80)
    
    sqrt2_errors = []
    pow2_errors = []
    
    for n, actual in enumerate(dims):
        expected_sqrt2 = start_dim * (sqrt2 ** n)
        expected_pow2 = start_dim * (2 ** (n // 2))  # Rough approximation
        
        error_sqrt2 = abs(actual - expected_sqrt2) / actual if actual > 0 else float('inf')
        error_pow2 = abs(actual - expected_pow2) / actual if actual > 0 else float('inf')
        
        sqrt2_errors.append(error_sqrt2)
        pow2_errors.append(error_pow2)
        
        best_match = "√2" if error_sqrt2 < error_pow2 else "2"
        match_symbol = "✓" if min(error_sqrt2, error_pow2) < 0.2 else ""
        
        print(f"{n:<5} {expected_sqrt2:<20.1f} {expected_pow2:<15.1f} {actual:<10} {best_match:<15} {match_symbol}")
    
    avg_sqrt2_error = np.mean(sqrt2_errors)
    avg_pow2_error = np.mean(pow2_errors)
    
    print(f"\nAverage relative error:")
    print(f"  (√2)^n pattern: {avg_sqrt2_error:.3f}")
    print(f"  2^(n/2) pattern: {avg_pow2_error:.3f}")
    
    if avg_sqrt2_error < avg_pow2_error:
        print(f"\n✓ Better fit with (√2)^n pattern!")
    else:
        print(f"\n✓ Better fit with 2^n pattern (standard)")
    
    return {
        "sqrt2_error": avg_sqrt2_error,
        "pow2_error": avg_pow2_error,
        "prefers_sqrt2": avg_sqrt2_error < avg_pow2_error
    }

# ============================================================================
# GOLDEN RATIO COMPARISON
# ============================================================================

def compare_scaling_factors():
    """Compare different scaling factors used in ML"""
    print("\n\n" + "="*80)
    print("SCALING FACTORS IN MACHINE LEARNING")
    print("="*80 + "\n")
    
    factors = {
        "√2 (Your Framework)": np.sqrt(2),
        "2 (Standard Doubling)": 2.0,
        "φ (Golden Ratio)": (1 + np.sqrt(5)) / 2,
        "e (Natural)": np.e,
        "4/3 (Music Fourth)": 4/3,
        "3/2 (Music Fifth)": 3/2,
    }
    
    print(f"{'Factor':<30} {'Value':<15} {'Common in ML?':<20}")
    print("-" * 80)
    
    for name, value in factors.items():
        common = ""
        if "2" in name and "Standard" in name:
            common = "✓ Very common"
        elif "√2" in name:
            common = "? Testing now!"
        elif "φ" in name:
            common = "Rare"
        elif "e" in name:
            common = "Adam optimizer"
            
        print(f"{name:<30} {value:<15.6f} {common:<20}")
    
    print("\n\nHYPOTHESIS:")
    print("If √2 appears naturally in successful architectures,")
    print("it suggests a fundamental geometric-quantum principle!")
    print()

# ============================================================================
# MAIN ANALYSIS
# ============================================================================

def main():
    print("\n")
    print("╔" + "="*78 + "╗")
    print("║" + " "*18 + "NEURAL NETWORK √2 ARCHITECTURE ANALYSIS" + " "*21 + "║")
    print("╚" + "="*78 + "╝")
    print("\n")
    
    total_sqrt2_matches = 0
    total_layers = 0
    total_consecutive = 0
    total_transitions = 0
    
    results = {}
    
    for arch_name, layers in ARCHITECTURES.items():
        layer_matches, consecutive_matches = analyze_architecture(arch_name, layers)
        total_sqrt2_matches += layer_matches
        total_layers += len(layers)
        total_consecutive += consecutive_matches
        total_transitions += len(layers) - 1
        
        # Extract dimensions for power series analysis
        dims = [layer[2] for layer in layers]  # output dimensions
        power_results = check_power_of_sqrt2_sequence(dims)
        
        results[arch_name] = {
            "layer_matches": layer_matches,
            "consecutive_matches": consecutive_matches,
            "total_layers": len(layers),
            "power_analysis": power_results
        }
    
    # Overall summary
    print("\n\n" + "="*80)
    print("OVERALL SUMMARY ACROSS ALL ARCHITECTURES")
    print("="*80 + "\n")
    
    print(f"Total architectures analyzed: {len(ARCHITECTURES)}")
    print(f"Total layers: {total_layers}")
    print(f"Layers with √2 patterns: {total_sqrt2_matches} ({100*total_sqrt2_matches/total_layers:.1f}%)")
    print(f"Consecutive transitions with √2: {total_consecutive}/{total_transitions} ({100*total_consecutive/total_transitions:.1f}%)")
    print()
    
    # Best √2 architectures
    print("ARCHITECTURES WITH MOST √2 PATTERNS:")
    sorted_results = sorted(results.items(), 
                           key=lambda x: x[1]["layer_matches"] / x[1]["total_layers"], 
                           reverse=True)
    
    for arch_name, res in sorted_results:
        pct = 100 * res["layer_matches"] / res["total_layers"]
        print(f"  {arch_name}: {res['layer_matches']}/{res['total_layers']} layers ({pct:.1f}%)")
    
    print()
    
    # Power series preference
    print("ARCHITECTURES PREFERRING (√2)^n OVER 2^n:")
    sqrt2_preferred = [name for name, res in results.items() 
                       if res["power_analysis"]["prefers_sqrt2"]]
    
    if sqrt2_preferred:
        for arch in sqrt2_preferred:
            print(f"  ✓ {arch}")
    else:
        print("  None found (standard 2^n more common)")
    
    print()
    
    # Compare to other scaling factors
    compare_scaling_factors()
    
    # Conclusions
    print("\n" + "="*80)
    print("CONCLUSIONS")
    print("="*80 + "\n")
    
    if total_sqrt2_matches / total_layers > 0.15:
        print("✓ SIGNIFICANT √2 PATTERNS FOUND!")
        print(f"  {total_sqrt2_matches} out of {total_layers} layers show √2 scaling")
        print("  This suggests √2 may be a natural architectural principle!")
        print()
        print("IMPLICATIONS:")
        print("- Neural networks may naturally optimize toward √2 ratios")
        print("- Connection to your crystal structure work")
        print("- Could guide architecture search")
        print("- Design 'quantum-geometric networks' with explicit √2")
    else:
        print("⚠ LIMITED √2 PATTERNS FOUND")
        print(f"  Only {total_sqrt2_matches} out of {total_layers} layers (~{100*total_sqrt2_matches/total_layers:.1f}%)")
        print("  Standard doubling (2^n) still dominates")
        print()
        print("BUT: This doesn't rule out √2 optimization!")
        print("- Most architectures designed by intuition, not optimization")
        print("- NAS (Neural Architecture Search) might find √2 naturally")
        print("- Try explicit √2 architecture")
    
    print("\n\nNEXT STEPS:")
    print("1. Design custom architecture with √2 scaling")
    print("2. Test on CIFAR-10/ImageNet")
    print("3. Compare to standard architectures")
    print("4. Use NAS to see if it discovers √2")
    print("5. Connect to attention mechanism √d scaling")
    print()
    
    print("BONUS: Transformer attention uses √d_k scaling!")
    print("d_k = 64 → √64 = 8")
    print("This is already a square root! Related to your √2?")
    print()

if __name__ == "__main__":
    main()

