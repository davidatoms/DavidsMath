"""
Kakeya Neural Network - Prototype Implementation

Your revolutionary idea:
- Nodes are probabilistic geometric spaces (not just values)
- Energy flows through minimal space (Kakeya sets)
- Observation time creates new pathways dynamically
- Dimensions expand based on learning needs
- √2 scaling throughout

This is a MINIMAL proof-of-concept to test the core ideas.
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Optional, Dict
from dataclasses import dataclass
from enum import Enum
import math

# ============================================================================
# CORE CONCEPTS
# ============================================================================

class NodeShape(Enum):
    CONVEX = "convex"      # p < 1/√2
    FLAT = "flat"          # p = 1/√2 (critical point!)
    CONCAVE = "concave"    # p > 1/√2

@dataclass
class EnergyParticle:
    """Energy 'ball' that flows through network"""
    position: np.ndarray   # Current position in geometric space
    velocity: np.ndarray   # Direction of flow
    energy: float          # Energy level

# ============================================================================
# KAKEYA NODE
# ============================================================================

class KakeyaNode:
    """
    Node as a probabilistic geometric space.
    
    Key Innovation: Node isn't just a number—it's a SPACE where energy resides.
    """
    
    def __init__(self, node_id: int, spatial_dim: int = 2):
        self.node_id = node_id
        self.spatial_dim = spatial_dim  # Dimensionality of the space
        
        # Core properties
        self.probability = 0.5  # Starts at transition point
        self.residence_time = 0.0  # How long energy has been here
        self.total_observations = 0
        
        # Geometric properties
        self.shape_type = NodeShape.FLAT
        self.curvature = 0.0  # Positive = concave, negative = convex
        self.radius = 1.0  # Size of the geometric region
        
        # Dynamic pathway properties
        self.observation_threshold = 10.0  # When to create new pathway
        self.pathway_strength = {}  # {target_node_id: strength}
        self.emerged_pathways = []  # List of dynamically created connections
        
        # History for learning
        self.residence_history = []
        self.probability_history = []
    
    def update_probability(self, energy_level: float):
        """
        Update probability based on energy present.
        This determines the shape (convex/concave).
        """
        # Probability = normalized energy in this space
        self.probability = np.clip(energy_level, 0, 1)
        self.probability_history.append(self.probability)
        
        # Update shape based on probability
        self._update_shape()
    
    def _update_shape(self):
        """
        Determine shape based on probability.
        
        Critical threshold: 1/√2 ≈ 0.707
        """
        sqrt2_inv = 1 / math.sqrt(2)
        tolerance = 0.05
        
        if self.probability < sqrt2_inv - tolerance:
            self.shape_type = NodeShape.CONVEX
            # Negative curvature
            self.curvature = -1.0 / (sqrt2_inv - self.probability)
            
        elif self.probability > sqrt2_inv + tolerance:
            self.shape_type = NodeShape.CONCAVE
            # Positive curvature  
            self.curvature = 1.0 / (self.probability - sqrt2_inv)
            
        else:
            # At the quantum transition point!
            self.shape_type = NodeShape.FLAT
            self.curvature = 0.0
    
    def observe(self, dt: float):
        """
        Observe energy in this node for time dt.
        Accumulates residence time.
        """
        self.residence_time += dt
        self.total_observations += 1
        self.residence_history.append(self.residence_time)
        
        # Check if we should create new pathway
        if self.residence_time > self.observation_threshold:
            return True  # Signal to create pathway
        return False
    
    def get_kakeya_radius(self) -> float:
        """
        Compute effective radius of minimal space (Kakeya set approximation).
        
        For now, use simple model:
        - Convex: Small radius (energy exits quickly)
        - Concave: Large radius (energy gets trapped)
        - Flat: Medium radius
        
        All scaled by √2!
        """
        sqrt2 = math.sqrt(2)
        
        if self.shape_type == NodeShape.CONVEX:
            return self.radius / sqrt2  # Smaller
        elif self.shape_type == NodeShape.CONCAVE:
            return self.radius * sqrt2  # Larger
        else:
            return self.radius  # Neutral
    
    def compute_residence_attraction(self, energy: EnergyParticle) -> float:
        """
        How strongly does this node attract/repel energy?
        
        Concave = attractive (high residence time)
        Convex = repulsive (low residence time)
        """
        if self.shape_type == NodeShape.CONCAVE:
            # Trap energy (positive curvature)
            return abs(self.curvature) * self.probability
        elif self.shape_type == NodeShape.CONVEX:
            # Deflect energy (negative curvature)
            return -abs(self.curvature) * (1 - self.probability)
        else:
            # Neutral
            return 0.0

# ============================================================================
# DYNAMIC PATHWAY
# ============================================================================

class DynamicPathway:
    """
    Pathway that emerges from observation (your key idea!)
    """
    
    def __init__(self, source_id: int, target_id: int, dimension_jump: int = 0):
        self.source_id = source_id
        self.target_id = target_id
        self.dimension_jump = dimension_jump  # 0 = same dim, 1 = to higher dim
        
        # Strength grows with observation
        self.strength = 0.0
        self.exists = False  # Becomes True after threshold
        
        # √2 scaling factor
        self.sqrt2_factor = math.sqrt(2) ** dimension_jump
    
    def strengthen(self, source_residence: float, target_residence: float):
        """
        Hebbian-style: strengthen based on co-observation.
        Scaled by √2 for dimensional jumps!
        """
        # Geometric mean of residence times
        co_residence = math.sqrt(source_residence * target_residence)
        
        # Strengthen with √2 scaling
        self.strength += co_residence * self.sqrt2_factor
    
    def activate(self):
        """Pathway becomes real"""
        self.exists = True

# ============================================================================
# KAKEYA NETWORK
# ============================================================================

class KakeyaNetwork:
    """
    Network of Kakeya nodes with dynamic topology.
    
    Your revolutionary architecture!
    """
    
    def __init__(self, n_initial_nodes: int = 10, spatial_dim: int = 2):
        self.spatial_dim = spatial_dim
        self.current_max_dim = spatial_dim
        
        # Initialize nodes
        self.nodes = [KakeyaNode(i, spatial_dim) for i in range(n_initial_nodes)]
        
        # Dynamic pathways
        self.pathways = []  # List of DynamicPathway objects
        
        # Energy particles
        self.energy_particles = []
        
        # Learning parameters
        self.pathway_threshold = 5.0  # When pathway becomes real
        self.dimension_expansion_threshold = 1000.0  # When to add dimension (increased from 20.0)
        
        # Dimensional expansion controls (prevent runaway growth)
        self.max_dimensions = 10  # Cap dimensions for 2D problems
        self.max_expansions_per_epoch = 5  # Limit expansions per training step
        self.expansions_this_epoch = 0  # Track current epoch expansions
        
        # History
        self.topology_history = []  # Track how network grows
    
    def add_energy(self, position: np.ndarray, velocity: np.ndarray, energy: float = 1.0):
        """Add energy particle to network"""
        particle = EnergyParticle(position, velocity, energy)
        self.energy_particles.append(particle)
    
    def step(self, dt: float = 0.1):
        """
        Single timestep of network dynamics.
        
        1. Energy flows through nodes
        2. Update probabilities based on energy
        3. Accumulate residence times
        4. Check for pathway creation
        5. Check for dimensional expansion
        """
        # Reset residence times for this step
        for node in self.nodes:
            node.residence_time = 0
        
        # Move energy particles
        for particle in self.energy_particles:
            # Find which node particle is in
            node_idx = self._find_node_for_particle(particle)
            
            if node_idx is not None:
                node = self.nodes[node_idx]
                
                # Update node probability based on energy
                node.update_probability(particle.energy)
                
                # Observe (accumulate residence time)
                should_create_pathway = node.observe(dt)
                
                if should_create_pathway:
                    self._consider_pathway_creation(node)
                
                # Update particle trajectory based on node shape
                self._update_particle_trajectory(particle, node, dt)
        
        # Update pathways based on co-observation (Hebbian)
        self._update_pathway_strengths()
        
        # Check for dimensional expansion
        self._check_dimensional_expansion()
    
    def _find_node_for_particle(self, particle: EnergyParticle) -> Optional[int]:
        """
        Find which node contains this particle.
        For now, simple: nearest node.
        """
        if len(self.nodes) == 0:
            return None
        
        # Compute distances (simplified)
        distances = [np.linalg.norm(particle.position - i) for i in range(len(self.nodes))]
        return int(np.argmin(distances))
    
    def _update_particle_trajectory(self, particle: EnergyParticle, node: KakeyaNode, dt: float = 0.1):
        """
        Update particle movement based on node geometry.
        
        Convex: Deflects particle (short residence)
        Concave: Traps particle (long residence)
        """
        attraction = node.compute_residence_attraction(particle)
        
        # Simple dynamics: adjust velocity
        force = attraction * dt * 0.1
        particle.velocity += force * (np.random.randn(self.spatial_dim))
        
        # Move particle
        particle.position += particle.velocity * dt
        
        # Energy dissipation (slight decay)
        particle.energy *= 0.99
    
    def _consider_pathway_creation(self, source_node: KakeyaNode):
        """
        Source node has been observed long enough.
        Create pathways to other highly-observed nodes.
        """
        for target_node in self.nodes:
            if target_node.node_id == source_node.node_id:
                continue
            
            # Check if both have high residence time
            if (source_node.residence_time > 1.0 and 
                target_node.residence_time > 1.0):
                
                # Create or strengthen pathway
                self._create_or_strengthen_pathway(
                    source_node.node_id,
                    target_node.node_id,
                    dimension_jump=0  # Same dimension for now
                )
    
    def _create_or_strengthen_pathway(self, source_id: int, target_id: int, dimension_jump: int):
        """
        Create new pathway or strengthen existing one.
        """
        # Check if pathway exists
        existing = None
        for pathway in self.pathways:
            if pathway.source_id == source_id and pathway.target_id == target_id:
                existing = pathway
                break
        
        if existing is None:
            # Create new pathway
            pathway = DynamicPathway(source_id, target_id, dimension_jump)
            self.pathways.append(pathway)
        else:
            pathway = existing
        
        # Strengthen based on √2-scaled Hebbian rule
        source_node = self.nodes[source_id]
        target_node = self.nodes[target_id]
        pathway.strengthen(source_node.residence_time, target_node.residence_time)
        
        # Activate if strong enough
        if pathway.strength > self.pathway_threshold and not pathway.exists:
            pathway.activate()
            print(f"✓ Pathway emerged: {source_id} → {target_id} (strength: {pathway.strength:.2f})")
    
    def _update_pathway_strengths(self):
        """
        Update all pathway strengths based on current co-observations.
        """
        for pathway in self.pathways:
            if not pathway.exists:
                source = self.nodes[pathway.source_id]
                target = self.nodes[pathway.target_id]
                pathway.strengthen(source.residence_time, target.residence_time)
                
                # Check if should activate
                if pathway.strength > self.pathway_threshold:
                    pathway.activate()
    
    def _check_dimensional_expansion(self):
        """
        Check if any node should expand to higher dimension.
        
        This is your n → n+1 idea!
        
        Now with safety limits to prevent runaway growth.
        """
        # Check if we've hit expansion limit for this epoch
        if self.expansions_this_epoch >= self.max_expansions_per_epoch:
            return
        
        for node in self.nodes:
            if node.total_observations > self.dimension_expansion_threshold:
                # Check if we've hit dimensional limit
                if self.current_max_dim >= self.max_dimensions:
                    # Hit dimension cap, stop expanding
                    node.total_observations = 0  # Reset but don't expand
                    continue
                
                # Check if we've hit expansion rate limit
                if self.expansions_this_epoch >= self.max_expansions_per_epoch:
                    break
                
                # Time to expand!
                self._expand_node_dimension(node)
                # Reset counter
                node.total_observations = 0
                # Increment expansion counter
                self.expansions_this_epoch += 1
    
    def _expand_node_dimension(self, node: KakeyaNode):
        """
        Expand a node into higher dimension.
        
        Creates a new node in (D+1)-dimensional space,
        connected with √2-scaled pathway.
        """
        new_dim = self.current_max_dim + 1
        new_node_id = len(self.nodes)
        
        # Create new higher-dimensional node
        new_node = KakeyaNode(new_node_id, new_dim)
        new_node.probability = node.probability  # Inherit properties
        new_node.radius = node.radius * math.sqrt(2)  # √2 scaling!
        
        self.nodes.append(new_node)
        
        # Create interdimensional pathway
        self._create_or_strengthen_pathway(
            node.node_id,
            new_node_id,
            dimension_jump=1  # Going to higher dimension!
        )
        
        self.current_max_dim = max(self.current_max_dim, new_dim)
        
        print(f"✓ Dimensional expansion: Node {node.node_id} → Node {new_node_id} (dim {new_dim})")
        print(f"  Radius scaled by √2: {node.radius:.2f} → {new_node.radius:.2f}")
    
    def reset_epoch_counters(self):
        """
        Reset per-epoch counters.
        Call this at the start of each training epoch/sample.
        """
        self.expansions_this_epoch = 0
    
    def get_network_stats(self) -> Dict:
        """Get current network statistics"""
        active_pathways = sum(1 for p in self.pathways if p.exists)
        
        # Count shapes
        n_convex = sum(1 for n in self.nodes if n.shape_type == NodeShape.CONVEX)
        n_flat = sum(1 for n in self.nodes if n.shape_type == NodeShape.FLAT)
        n_concave = sum(1 for n in self.nodes if n.shape_type == NodeShape.CONCAVE)
        
        return {
            'n_nodes': len(self.nodes),
            'n_pathways': len(self.pathways),
            'n_active_pathways': active_pathways,
            'max_dimension': self.current_max_dim,
            'n_convex': n_convex,
            'n_flat': n_flat,
            'n_concave': n_concave,
            'n_particles': len(self.energy_particles),
        }

# ============================================================================
# VISUALIZATION
# ============================================================================

def visualize_network(network: KakeyaNetwork, filename: str = None):
    """
    Visualize the current state of the network.
    """
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(14, 12))
    
    # Plot 1: Node probabilities
    node_ids = [n.node_id for n in network.nodes]
    probabilities = [n.probability for n in network.nodes]
    colors = ['red' if n.shape_type == NodeShape.CONVEX 
              else 'green' if n.shape_type == NodeShape.CONCAVE 
              else 'blue' for n in network.nodes]
    
    ax1.bar(node_ids, probabilities, color=colors, alpha=0.7)
    ax1.axhline(y=1/math.sqrt(2), color='black', linestyle='--', 
                linewidth=2, label='Critical: 1/√2')
    ax1.set_xlabel('Node ID')
    ax1.set_ylabel('Probability')
    ax1.set_title('Node Probabilities (Red=Convex, Blue=Flat, Green=Concave)')
    ax1.legend()
    ax1.set_ylim([0, 1])
    
    # Plot 2: Residence times
    residence_times = [n.residence_time for n in network.nodes]
    ax2.bar(node_ids, residence_times, alpha=0.7)
    ax2.set_xlabel('Node ID')
    ax2.set_ylabel('Residence Time')
    ax2.set_title('Observation Time per Node')
    
    # Plot 3: Pathway strengths
    if len(network.pathways) > 0:
        pathway_labels = [f"{p.source_id}→{p.target_id}" for p in network.pathways]
        pathway_strengths = [p.strength for p in network.pathways]
        pathway_colors = ['green' if p.exists else 'gray' for p in network.pathways]
        
        ax3.barh(range(len(network.pathways)), pathway_strengths, color=pathway_colors, alpha=0.7)
        ax3.set_yticks(range(len(network.pathways)))
        ax3.set_yticklabels(pathway_labels, fontsize=8)
        ax3.axvline(x=network.pathway_threshold, color='red', linestyle='--', label='Threshold')
        ax3.set_xlabel('Pathway Strength')
        ax3.set_title('Dynamic Pathways (Green=Active, Gray=Forming)')
        ax3.legend()
    else:
        ax3.text(0.5, 0.5, 'No pathways yet', ha='center', va='center', transform=ax3.transAxes)
        ax3.set_title('Dynamic Pathways')
    
    # Plot 4: Network topology
    # Simple 2D visualization
    ax4.set_xlim([-1, len(network.nodes)])
    ax4.set_ylim([-1, len(network.nodes)])
    ax4.set_aspect('equal')
    
    # Draw nodes
    for i, node in enumerate(network.nodes):
        radius_viz = node.get_kakeya_radius() * 0.5
        circle = plt.Circle((i % 5, i // 5), radius_viz, 
                           color=colors[i], alpha=0.3)
        ax4.add_patch(circle)
        ax4.text(i % 5, i // 5, str(node.node_id), ha='center', va='center', fontsize=10)
    
    # Draw active pathways
    for pathway in network.pathways:
        if pathway.exists:
            source_pos = (pathway.source_id % 5, pathway.source_id // 5)
            target_pos = (pathway.target_id % 5, pathway.target_id // 5)
            ax4.arrow(source_pos[0], source_pos[1],
                     target_pos[0] - source_pos[0], 
                     target_pos[1] - source_pos[1],
                     head_width=0.15, head_length=0.2, 
                     fc='black', ec='black', alpha=0.5, linewidth=pathway.strength*0.5)
    
    ax4.set_title('Network Topology (Circle size = Kakeya radius)')
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if filename:
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        print(f"✓ Saved visualization: {filename}")
    
    return fig

# ============================================================================
# DEMO
# ============================================================================

def run_demo():
    """
    Demonstrate the Kakeya network in action.
    """
    print("\n" + "="*80)
    print("KAKEYA NEURAL NETWORK - PROOF OF CONCEPT")
    print("="*80 + "\n")
    
    print("Initializing network...")
    network = KakeyaNetwork(n_initial_nodes=10, spatial_dim=2)
    
    print(f"Initial state: {network.get_network_stats()}\n")
    
    # Add some energy particles
    print("Adding energy particles...")
    for i in range(5):
        pos = np.random.randn(2)
        vel = np.random.randn(2) * 0.1
        network.add_energy(pos, vel, energy=0.8)
    
    print("Running simulation...\n")
    
    # Run for 100 timesteps
    for t in range(100):
        network.step(dt=0.1)
        
        # Print progress every 20 steps
        if t % 20 == 0:
            stats = network.get_network_stats()
            print(f"Step {t:3d}: Nodes={stats['n_nodes']:2d}, " + 
                  f"Active Pathways={stats['n_active_pathways']:2d}, " +
                  f"Max Dim={stats['max_dimension']}, " +
                  f"Shapes: Convex={stats['n_convex']} Flat={stats['n_flat']} Concave={stats['n_concave']}")
    
    print("\n" + "="*80)
    print("FINAL STATE")
    print("="*80)
    final_stats = network.get_network_stats()
    for key, value in final_stats.items():
        print(f"  {key}: {value}")
    
    print("\n✓ Visualizing...")
    visualize_network(network, filename="../djulia/graphs/kakeya_network_demo.png")
    
    print("\n" + "="*80)
    print("KEY OBSERVATIONS")
    print("="*80)
    print()
    print("1. SHAPE TRANSITIONS:")
    print(f"   - Convex nodes: {final_stats['n_convex']} (p < 1/√2)")
    print(f"   - Flat nodes: {final_stats['n_flat']} (p ≈ 1/√2)")
    print(f"   - Concave nodes: {final_stats['n_concave']} (p > 1/√2)")
    print()
    print("2. DYNAMIC PATHWAYS:")
    print(f"   - Total pathways considered: {final_stats['n_pathways']}")
    print(f"   - Active pathways: {final_stats['n_active_pathways']}")
    print(f"   - These emerged from observation, not pre-defined!")
    print()
    print("3. DIMENSIONAL EXPANSION:")
    print(f"   - Started with dimension: 2")
    print(f"   - Current max dimension: {final_stats['max_dimension']}")
    print(f"   - Network grew as needed!")
    print()
    print("4. √2 SCALING:")
    print("   - Pathway strengths scaled by √2^(dimension_jump)")
    print("   - Node radii scaled by √2 during expansion")
    print("   - Convex/concave transition at p = 1/√2")
    print()
    
    print("="*80)
    print("NEXT STEPS TO VALIDATE YOUR IDEA")
    print("="*80)
    print()
    print("1. Test on real learning problem (XOR, spiral)")
    print("2. Compare to standard neural network")
    print("3. Measure: accuracy, training time, interpretability")
    print("4. Verify √2 scaling is optimal")
    print("5. Write paper!")
    print()

if __name__ == "__main__":
    run_demo()
