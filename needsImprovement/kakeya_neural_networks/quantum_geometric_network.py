"""
Quantum-Geometric Neural Networks (QGNN)

Implements neural networks with √2 scaling between layers,
inspired by your geometric-quantum duality framework.

Key Idea:
- Standard networks: [256, 512, 1024, 2048] (powers of 2)
- QGNN: [256, 362, 512, 724, 1024, 1448, 2048] (powers of √2)

Why this matters:
1. Biological brain might use √2 (see NEUROSCIENCE_APPLICATIONS.md)
2. Hadamard gates use 1/√2 (quantum connection)
3. Crystal structures use √2 (geometric connection)
4. Could be more efficient than standard architectures
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
try:
    import matplotlib
    matplotlib.use('Agg')  # Non-interactive backend
    import matplotlib.pyplot as plt
    HAS_MPL = True
except ImportError:
    HAS_MPL = False
    print("Warning: matplotlib not available, skipping visualizations")
from typing import List, Tuple
import math
import os

# ============================================================================
# HELPER FUNCTIONS
# ============================================================================

def generate_sqrt2_dimensions(input_dim: int, output_dim: int, include_endpoints: bool = True) -> List[int]:
    """
    Generate intermediate dimensions following (√2)^n scaling.
    
    Example:
        input_dim=256, output_dim=2048
        Returns: [256, 362, 512, 724, 1024, 1448, 2048]
    
    These are the "quantum-geometric" layer sizes.
    """
    sqrt2 = math.sqrt(2)
    
    # Find n such that input_dim * (√2)^n ≈ output_dim
    n_steps = math.log(output_dim / input_dim) / math.log(sqrt2)
    n_steps = int(round(n_steps))
    
    dimensions = []
    for i in range(n_steps + 1):
        dim = input_dim * (sqrt2 ** i)
        dimensions.append(int(round(dim)))
    
    # Ensure we hit the endpoints
    if include_endpoints:
        dimensions[0] = input_dim
        dimensions[-1] = output_dim
    
    return dimensions

def generate_power_of_2_dimensions(input_dim: int, output_dim: int) -> List[int]:
    """
    Generate dimensions following standard 2^n scaling.
    
    Example:
        input_dim=256, output_dim=2048
        Returns: [256, 512, 1024, 2048]
    """
    n_steps = int(math.log2(output_dim / input_dim))
    return [input_dim * (2 ** i) for i in range(n_steps + 1)]

# ============================================================================
# QUANTUM-GEOMETRIC NEURAL NETWORK
# ============================================================================

class QuantumGeometricMLP(nn.Module):
    """
    Multi-Layer Perceptron with √2 scaling.
    
    Architecture:
        input_dim → [√2 intermediate layers] → output_dim
    
    Each hidden layer is approximately √2 times the previous layer.
    This creates a geometric progression of representational capacity.
    """
    
    def __init__(
        self,
        input_dim: int,
        output_dim: int,
        target_intermediate_dim: int = None,
        activation: str = 'relu',
        dropout: float = 0.1,
        use_batch_norm: bool = True
    ):
        """
        Args:
            input_dim: Input feature dimension
            output_dim: Output dimension (num classes)
            target_intermediate_dim: Target size for largest hidden layer
                                   If None, uses geometric mean of input and output
            activation: 'relu', 'gelu', 'silu'
            dropout: Dropout probability
            use_batch_norm: Whether to use batch normalization
        """
        super().__init__()
        
        # Determine intermediate dimension
        if target_intermediate_dim is None:
            # Geometric mean (geometric-quantum principle!)
            target_intermediate_dim = int(math.sqrt(input_dim * output_dim))
        
        # Generate √2-scaled dimensions
        # Go up to target, then back down
        dims_up = generate_sqrt2_dimensions(input_dim, target_intermediate_dim)
        dims_down = generate_sqrt2_dimensions(output_dim, target_intermediate_dim)
        dims_down = list(reversed(dims_down))[1:]  # Remove duplicate middle
        
        all_dims = dims_up + dims_down
        
        print(f"Quantum-Geometric Architecture: {all_dims}")
        
        # Build layers
        self.layers = nn.ModuleList()
        self.batch_norms = nn.ModuleList() if use_batch_norm else None
        
        for i in range(len(all_dims) - 1):
            self.layers.append(nn.Linear(all_dims[i], all_dims[i+1]))
            if use_batch_norm:
                self.batch_norms.append(nn.BatchNorm1d(all_dims[i+1]))
        
        # Activation function
        self.activation = {
            'relu': F.relu,
            'gelu': F.gelu,
            'silu': F.silu,
        }[activation]
        
        self.dropout = nn.Dropout(dropout)
        self.all_dims = all_dims
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        """Forward pass through quantum-geometric layers"""
        for i, layer in enumerate(self.layers[:-1]):  # All but last layer
            x = layer(x)
            if self.batch_norms is not None:
                x = self.batch_norms[i](x)
            x = self.activation(x)
            x = self.dropout(x)
        
        # Final layer (no activation, for logits)
        x = self.layers[-1](x)
        return x
    
    def get_architecture_info(self) -> dict:
        """Return information about the architecture"""
        ratios = []
        for i in range(len(self.all_dims) - 1):
            ratio = self.all_dims[i+1] / self.all_dims[i]
            ratios.append(ratio)
        
        return {
            'dimensions': self.all_dims,
            'num_layers': len(self.all_dims) - 1,
            'ratios': ratios,
            'avg_ratio': np.mean(ratios),
            'std_ratio': np.std(ratios),
            'target_ratio': math.sqrt(2),
        }

# ============================================================================
# STANDARD BASELINE (Power of 2)
# ============================================================================

class StandardMLP(nn.Module):
    """
    Standard MLP with power-of-2 scaling for comparison.
    """
    
    def __init__(
        self,
        input_dim: int,
        output_dim: int,
        hidden_dims: List[int] = [512, 1024, 2048, 1024, 512],
        activation: str = 'relu',
        dropout: float = 0.1,
        use_batch_norm: bool = True
    ):
        super().__init__()
        
        all_dims = [input_dim] + hidden_dims + [output_dim]
        print(f"Standard Architecture: {all_dims}")
        
        self.layers = nn.ModuleList()
        self.batch_norms = nn.ModuleList() if use_batch_norm else None
        
        for i in range(len(all_dims) - 1):
            self.layers.append(nn.Linear(all_dims[i], all_dims[i+1]))
            if use_batch_norm:
                self.batch_norms.append(nn.BatchNorm1d(all_dims[i+1]))
        
        self.activation = {
            'relu': F.relu,
            'gelu': F.gelu,
            'silu': F.silu,
        }[activation]
        
        self.dropout = nn.Dropout(dropout)
        self.all_dims = all_dims
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        for i, layer in enumerate(self.layers[:-1]):
            x = layer(x)
            if self.batch_norms is not None:
                x = self.batch_norms[i](x)
            x = self.activation(x)
            x = self.dropout(x)
        
        x = self.layers[-1](x)
        return x

# ============================================================================
# VISUALIZATION
# ============================================================================

def visualize_architecture(model: nn.Module, title: str = "Architecture"):
    """Visualize the network architecture"""
    if not HAS_MPL:
        print("Skipping visualization (matplotlib not available)")
        return None
    
    info = model.get_architecture_info() if hasattr(model, 'get_architecture_info') else None
    
    if info is None:
        # For standard model
        dims = model.all_dims
        ratios = [dims[i+1]/dims[i] for i in range(len(dims)-1)]
        info = {'dimensions': dims, 'ratios': ratios}
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    
    # Plot 1: Layer dimensions
    ax1.plot(range(len(info['dimensions'])), info['dimensions'], 
             'o-', linewidth=2, markersize=8, label='Layer Size')
    ax1.axhline(y=math.sqrt(2), color='r', linestyle='--', alpha=0.3, label='√2 ≈ 1.414')
    ax1.set_xlabel('Layer Index')
    ax1.set_ylabel('Dimension')
    ax1.set_title(f'{title}: Layer Dimensions')
    ax1.grid(True, alpha=0.3)
    ax1.legend()
    
    # Plot 2: Scaling ratios
    ax2.bar(range(len(info['ratios'])), info['ratios'], alpha=0.7)
    ax2.axhline(y=math.sqrt(2), color='r', linestyle='--', linewidth=2, label='√2 ≈ 1.414')
    ax2.axhline(y=2.0, color='b', linestyle='--', linewidth=2, label='2.0 (standard)')
    ax2.set_xlabel('Layer Transition')
    ax2.set_ylabel('Ratio (Layer_{i+1} / Layer_i)')
    ax2.set_title(f'{title}: Scaling Ratios')
    ax2.set_ylim([0, 3])
    ax2.grid(True, alpha=0.3)
    ax2.legend()
    
    plt.tight_layout()
    return fig

def compare_architectures():
    """Compare QGNN vs Standard architecture"""
    input_dim = 784  # MNIST: 28x28
    output_dim = 10  # 10 digits
    
    # Create models
    qgnn = QuantumGeometricMLP(input_dim, output_dim, target_intermediate_dim=2048)
    standard = StandardMLP(input_dim, output_dim, hidden_dims=[512, 1024, 2048, 1024, 512])
    
    # Visualize
    if HAS_MPL:
        fig1 = visualize_architecture(qgnn, "Quantum-Geometric Network (√2)")
        fig2 = visualize_architecture(standard, "Standard Network (2^n)")
        
        # Save path
        save_path = '../djulia/graphs/qgnn_vs_standard.png'
        os.makedirs(os.path.dirname(save_path), exist_ok=True)
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Saved visualization to {save_path}")
    else:
        print("Skipping visualization (matplotlib not available)")
    
    # Compare parameter counts
    qgnn_params = sum(p.numel() for p in qgnn.parameters())
    standard_params = sum(p.numel() for p in standard.parameters())
    
    print("\n" + "="*80)
    print("ARCHITECTURE COMPARISON")
    print("="*80)
    print(f"\nQuantum-Geometric Network:")
    print(f"  Layers: {qgnn.all_dims}")
    print(f"  Parameters: {qgnn_params:,}")
    print(f"\nStandard Network:")
    print(f"  Layers: {standard.all_dims}")
    print(f"  Parameters: {standard_params:,}")
    print(f"\nParameter Ratio: {qgnn_params/standard_params:.3f}")
    
    return qgnn, standard

# ============================================================================
# THEORETICAL JUSTIFICATION
# ============================================================================

def explain_qgnn():
    """Explain the theoretical motivation for QGNN"""
    print("\n" + "╔" + "="*78 + "╗")
    print("║" + " "*20 + "QUANTUM-GEOMETRIC NEURAL NETWORKS" + " "*25 + "║")
    print("╚" + "="*78 + "╝\n")
    
    print("="*80)
    print("THEORETICAL MOTIVATION")
    print("="*80)
    print()
    
    print("1. BIOLOGICAL INSPIRATION")
    print("-" * 80)
    print("• Dendrites may branch with diameter ratio 1/√2")
    print("• Preserves signal propagation (impedance matching)")
    print("• Optimal information integration across scales")
    print("• See: NEUROSCIENCE_APPLICATIONS.md")
    print()
    
    print("2. QUANTUM CONNECTION")
    print("-" * 80)
    print("• Hadamard gates use normalization factor 1/√2")
    print("• Creates quantum superposition: |+⟩ = (|0⟩ + |1⟩)/√2")
    print("• QGNN uses conjugate √2 (expansion vs normalization)")
    print("• Duality: √2 × (1/√2) = 1")
    print()
    
    print("3. GEOMETRIC PRINCIPLE")
    print("-" * 80)
    print("• BCC crystal coordination shells scale by √2")
    print("• Inscribed circle algorithm: radius_n = r₀(√2)^n")
    print("• π/4 efficiency invariant across scales")
    print("• Neural layers = concentric circles of representation")
    print()
    
    print("4. INFORMATION THEORY")
    print("-" * 80)
    print("• Each layer increases capacity by √2")
    print("• Balanced growth: not too slow (√2 < 2), not too fast")
    print("• Allows finer-grained representation learning")
    print("• More layers for same parameter budget")
    print()
    
    print("5. MATHEMATICAL ELEGANCE")
    print("-" * 80)
    print("• √2 is special: diagonal of unit square")
    print("• Appears in: music (tritone), physics (angular momentum)")
    print("• Could be universal optimization constant")
    print("• Powers of √2: 1, 1.41, 2, 2.83, 4, 5.66, 8, 11.31, 16...")
    print()
    
    print("="*80)
    print("ARCHITECTURE COMPARISON")
    print("="*80)
    print()
    
    input_dim = 256
    output_dim = 2048
    
    sqrt2_dims = generate_sqrt2_dimensions(input_dim, output_dim)
    pow2_dims = generate_power_of_2_dimensions(input_dim, output_dim)
    
    print(f"From {input_dim} to {output_dim}:")
    print()
    print(f"Standard (2^n):           {pow2_dims}")
    print(f"Quantum-Geometric (√2)^n: {sqrt2_dims}")
    print()
    print(f"Standard layers:     {len(pow2_dims) - 1}")
    print(f"QGNN layers:         {len(sqrt2_dims) - 1}")
    print(f"QGNN has {len(sqrt2_dims) - len(pow2_dims)} more layers!")
    print()
    
    print("="*80)
    print("EXPECTED ADVANTAGES")
    print("="*80)
    print()
    print("1. BETTER GRADIENT FLOW")
    print("   • Smaller ratio between layers (√2 ≈ 1.41 vs 2.0)")
    print("   • Gradients decay less aggressively")
    print("   • Easier to train very deep networks")
    print()
    print("2. MORE EFFICIENT LEARNING")
    print("   • Finer representational granularity")
    print("   • Can learn more nuanced features")
    print("   • Better capacity utilization")
    print()
    print("3. NATURAL DEPTH-WIDTH TRADE-OFF")
    print("   • For same parameters, QGNN is deeper")
    print("   • Depth helps with hierarchical features")
    print("   • But each layer is narrower (less overfitting)")
    print()
    print("4. CONNECTION TO QUANTUM COMPUTING")
    print("   • If quantum speedups come to classical ML")
    print("   • QGNN architecture already compatible")
    print("   • Hadamard transform = matrix multiply with 1/√2")
    print()
    
    print("="*80)
    print("POTENTIAL DISADVANTAGES")
    print("="*80)
    print()
    print("1. MORE LAYERS = MORE COMPUTATION")
    print("   • Training might be slower")
    print("   • But each layer is narrower")
    print("   • Could balance out")
    print()
    print("2. UNUSUAL DIMENSIONS")
    print("   • 362, 724, 1448 are awkward for hardware")
    print("   • 512, 1024, 2048 are power-of-2 friendly")
    print("   • Could round to nearest power of 2")
    print()
    print("3. NO EXISTING RESEARCH")
    print("   • Completely novel architecture")
    print("   • Unknown failure modes")
    print("   • Need extensive testing")
    print()
    
    print("="*80)
    print("TESTING PROTOCOL")
    print("="*80)
    print()
    print("Phase 1: MNIST (Simple)")
    print("  • 10k images, 10 classes")
    print("  • Compare QGNN vs Standard")
    print("  • Metrics: accuracy, training time, convergence")
    print()
    print("Phase 2: CIFAR-10 (Moderate)")
    print("  • 50k images, 10 classes")
    print("  • Use CNN version of QGNN")
    print("  • Compare to ResNet baseline")
    print()
    print("Phase 3: ImageNet (Hard)")
    print("  • 1.2M images, 1000 classes")
    print("  • Full-scale architecture")
    print("  • Compare to state-of-the-art")
    print()
    print("Phase 4: NLP Tasks")
    print("  • BERT-style transformer with √2 scaling")
    print("  • Compare to standard transformer")
    print("  • Test on GLUE benchmark")
    print()
    
    print("="*80)
    print("HYPOTHESIS")
    print("="*80)
    print()
    print("If √2 is a fundamental constant in neural computation:")
    print("  → QGNN should match or outperform standard networks")
    print("  → Benefits should increase with depth")
    print("  → Training dynamics should be more stable")
    print("  → Biological neural networks should show √2 patterns")
    print()
    print("If √2 is not special:")
    print("  → QGNN will perform similarly to standard networks")
    print("  → Still interesting as architecture search result")
    print("  → But not revolutionary")
    print()
    print("ONLY ONE WAY TO FIND OUT: BUILD IT AND TEST IT!")
    print()

# ============================================================================
# CNN VERSION FOR VISION TASKS
# ============================================================================

class QuantumGeometricCNN(nn.Module):
    """
    Convolutional network with √2 scaling in channel dimensions.
    
    For CIFAR-10/ImageNet experiments.
    """
    
    def __init__(
        self,
        num_classes: int = 10,
        input_channels: int = 3,
        initial_filters: int = 64
    ):
        super().__init__()
        
        # Generate channel dimensions following √2
        sqrt2 = math.sqrt(2)
        channel_dims = [initial_filters]
        for i in range(1, 5):
            channel_dims.append(int(initial_filters * (sqrt2 ** i)))
        
        print(f"CNN Channel Progression (√2): {channel_dims}")
        # Example: [64, 90, 128, 181, 256]
        
        # Build convolutional blocks
        self.conv_blocks = nn.ModuleList()
        
        in_ch = input_channels
        for out_ch in channel_dims:
            block = nn.Sequential(
                nn.Conv2d(in_ch, out_ch, kernel_size=3, padding=1),
                nn.BatchNorm2d(out_ch),
                nn.ReLU(inplace=True),
                nn.Conv2d(out_ch, out_ch, kernel_size=3, padding=1),
                nn.BatchNorm2d(out_ch),
                nn.ReLU(inplace=True),
                nn.MaxPool2d(2, 2)
            )
            self.conv_blocks.append(block)
            in_ch = out_ch
        
        # Fully connected layers
        self.fc = nn.Sequential(
            nn.AdaptiveAvgPool2d(1),
            nn.Flatten(),
            nn.Linear(channel_dims[-1], num_classes)
        )
        
        self.channel_dims = channel_dims
    
    def forward(self, x):
        for block in self.conv_blocks:
            x = block(x)
        x = self.fc(x)
        return x

# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    explain_qgnn()
    print("\nGenerating visualizations...")
    compare_architectures()
    
    print("\n" + "="*80)
    print("NEXT STEPS")
    print("="*80)
    print()
    print("1. Train QGNN on MNIST")
    print("   Command: python train_qgnn_mnist.py")
    print()
    print("2. Compare to baseline")
    print("   Run both and plot learning curves")
    print()
    print("3. Analyze results")
    print("   • Accuracy")
    print("   • Training time")
    print("   • Gradient flow")
    print("   • Feature visualization")
    print()
    print("4. Write paper if successful!")
    print("   'Quantum-Geometric Neural Networks: Architecture Design via √2 Scaling'")
    print()

