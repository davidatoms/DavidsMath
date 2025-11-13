-- Geometric Scaling Algorithm: Inscribed Circle in Square
-- Algorithm: Given a square with inscribed circle of radius r,
-- the diagonal from center to corner is r√2, which becomes
-- the new radius for the next iteration.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace ScalingAlgorithmInscribedCircleSquare

/-- A square with an inscribed circle -/
structure SquareWithInscribedCircle where
  radius : ℝ
  radius_positive : radius > 0

/-- Single iteration of geometric scaling: scale radius by √2 -/
noncomputable def scaleOnce (config : SquareWithInscribedCircle) : SquareWithInscribedCircle :=
  { radius := config.radius * Real.sqrt 2,
    radius_positive := by
      apply mul_pos config.radius_positive
      apply Real.sqrt_pos.mpr
      norm_num }

/-- The side length of the square (diameter of inscribed circle) -/
def squareSideLength (config : SquareWithInscribedCircle) : ℝ :=
  2 * config.radius

/-- The diagonal from center to corner of the square -/
noncomputable def diagonalToCorner (config : SquareWithInscribedCircle) : ℝ :=
  Real.sqrt (config.radius^2 + config.radius^2)

/-- Theorem: The diagonal equals radius * √2 -/
theorem diagonal_formula (config : SquareWithInscribedCircle) :
  diagonalToCorner config = config.radius * Real.sqrt 2 := by
  unfold diagonalToCorner
  rw [show config.radius^2 + config.radius^2 = 2 * config.radius^2 by ring]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.sqrt_sq (le_of_lt config.radius_positive)]
  ring

/-- Theorem: After one scaling, the new radius equals the old diagonal -/
theorem scale_once_equals_diagonal (config : SquareWithInscribedCircle) :
  (scaleOnce config).radius = diagonalToCorner config := by
  unfold scaleOnce diagonalToCorner
  simp
  rw [show config.radius^2 + config.radius^2 = 2 * config.radius^2 by ring]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.sqrt_sq (le_of_lt config.radius_positive)]
  ring

/-- Apply scaling n times -/
noncomputable def scaleNTimes (config : SquareWithInscribedCircle) : ℕ → SquareWithInscribedCircle
  | 0 => config
  | n + 1 => scaleOnce (scaleNTimes config n)

/-- Theorem: After n iterations, radius = initial_radius * (√2)^n -/
theorem scale_n_times_formula (config : SquareWithInscribedCircle) (n : ℕ) :
  (scaleNTimes config n).radius = config.radius * (Real.sqrt 2)^n := by
  induction n with
  | zero =>
    simp [scaleNTimes]
  | succ n ih =>
    simp [scaleNTimes, scaleOnce]
    rw [ih]
    rw [pow_succ]
    ring

/-- Example: Starting configuration with radius 5 -/
noncomputable def initialConfig : SquareWithInscribedCircle :=
  { radius := 5,
    radius_positive := by norm_num }

/-- Compute the configuration after n iterations starting from radius 5 -/
noncomputable def scaledConfig (n : ℕ) : SquareWithInscribedCircle :=
  scaleNTimes initialConfig n

/-- Theorem: After n iterations from radius 5, radius = 5 * (√2)^n -/
theorem scaled_config_formula (n : ℕ) :
  (scaledConfig n).radius = 5 * (Real.sqrt 2)^n := by
  unfold scaledConfig
  rw [scale_n_times_formula]
  simp [initialConfig]

/-- Example computations for specific iterations -/
example : (scaledConfig 0).radius = 5 := by
  simp [scaledConfig, scaleNTimes, initialConfig]

example : (scaledConfig 1).radius = 5 * Real.sqrt 2 := by
  rw [scaled_config_formula]
  simp

example : (scaledConfig 2).radius = 5 * 2 := by
  rw [scaled_config_formula]
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The scaling factor at each iteration -/
noncomputable def scalingFactor : ℝ := Real.sqrt 2

/-- Theorem: The scaling is geometric with ratio √2 -/
theorem geometric_scaling (config : SquareWithInscribedCircle) :
  (scaleOnce config).radius = scalingFactor * config.radius := by
  unfold scaleOnce scalingFactor
  ring

/-- Side length after n iterations starting from radius r -/
noncomputable def sideLengthAfterNIterations (initial_radius : ℝ) (n : ℕ) : ℝ :=
  2 * initial_radius * (Real.sqrt 2)^n

/-- Theorem: Side length grows geometrically -/
theorem side_length_geometric (r : ℝ) (n : ℕ) :
  sideLengthAfterNIterations r (n + 1) = Real.sqrt 2 * sideLengthAfterNIterations r n := by
  unfold sideLengthAfterNIterations
  rw [pow_succ]
  ring

end ScalingAlgorithmInscribedCircleSquare
