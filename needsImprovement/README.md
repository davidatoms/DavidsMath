# Needs Improvement

This folder contains explorations that showed promise but require significant work before being production-ready.

## What's Here

### Kakeya Neural Networks

**Status**: Geometric framework works perfectly, learning algorithm needs complete redesign

**What Works** ✓:
- √2 dimensional expansion (perfectly controlled)
- Geometric node shapes (convex/concave transitions at 1/√2)
- Dynamic topology growth
- Energy flow through minimal space
- Radius scaling by √2

**What Doesn't Work** ✗:
- Learning algorithm (no gradient descent)
- Training accuracy: ~50% (random guessing)
- Very slow inference (5 network steps per prediction)
- No proper backpropagation

**Test Results**:
- Standard MLP: 71% train, 68% test
- Kakeya Network: 47% train, 51% test

**Conclusion**: 
The geometric framework is mathematically sound and beautifully implemented. The problem is applying it to supervised learning without proper gradient-based optimization. This needs a complete learning algorithm redesign, not just tweaking.

**Next Steps** (if revisited):
1. Implement proper gradient descent
2. Add backpropagation through geometric transformations
3. Optimize inference speed
4. Test on simpler tasks first (regression, not classification)

---

## Philosophy

Not everything needs to be production-ready immediately. This folder preserves explorations that:
- Have solid mathematical foundations
- Show interesting properties
- Need more development time
- Might inspire future work

The geometric √2 framework is powerful. We just need to find the right application domain.

---

**Date Created**: November 14, 2025
**Reason**: Pivot to explore better use cases for geometric framework

