-- CobbDouglasMatrix.lean
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sort

namespace Econ

/-- Generalized Cobb–Douglas production function with n inputs. -/
structure CobbDouglasMatrix (n : ℕ) where
  A : ℝ                           -- total factor productivity
  α : Fin n → ℝ                   -- elasticity vector
  x : Fin n → ℝ                   -- input vector (K, L, K_AI, ...)
  hA : A > 0
  hα : ∀ i, α i > 0
  hx : ∀ i, x i ≥ 0

/-- Output function Y = A * exp( αᵀ · log(x) ) -/
noncomputable def output {n : ℕ} (cd : CobbDouglasMatrix n) : ℝ :=
  cd.A * Real.exp (Finset.univ.sum (λ i : Fin n => (cd.α i) * Real.log (cd.x i)))

/-- Marginal product of input i: ∂Y/∂xᵢ = Y * αᵢ / xᵢ -/
noncomputable def marginalProduct {n : ℕ} (cd : CobbDouglasMatrix n) (i : Fin n) : ℝ :=
  (output cd) * (cd.α i) / (cd.x i)

/-- Returns to scale: sum of αᵢ -/
def returnsToScale {n : ℕ} (cd : CobbDouglasMatrix n) : ℝ :=
  Finset.univ.sum (λ i : Fin n => cd.α i)

/-- Return on Investment (ROI) for input i: MPᵢ/xᵢ -/
noncomputable def roiInput {n : ℕ} (cd : CobbDouglasMatrix n) (i : Fin n) : ℝ :=
  if cd.x i > 0 then (marginalProduct cd i) / (cd.x i) else 0

/-- Get marginal product ranking (simplified version) -/
noncomputable def getMarginalProduct {n : ℕ} (cd : CobbDouglasMatrix n) (i : Fin n) : ℝ :=
  marginalProduct cd i

/-- Get ROI for specific input -/
noncomputable def getROI {n : ℕ} (cd : CobbDouglasMatrix n) (i : Fin n) : ℝ :=
  roiInput cd i

/-- Compare marginal products of two inputs -/
noncomputable def compareMarginalProducts {n : ℕ} (cd : CobbDouglasMatrix n) (i j : Fin n) : String :=
  let mpi := marginalProduct cd i
  let mpj := marginalProduct cd j
  if mpi > mpj then "Input " ++ toString i.val ++ " has higher marginal product"
  else if mpj > mpi then "Input " ++ toString j.val ++ " has higher marginal product"
  else "Equal marginal products"

/-- Compare ROIs of two inputs -/
noncomputable def compareROIs {n : ℕ} (cd : CobbDouglasMatrix n) (i j : Fin n) : String :=
  let roi_i := roiInput cd i
  let roi_j := roiInput cd j
  if roi_i > roi_j then "Input " ++ toString i.val ++ " has higher ROI"
  else if roi_j > roi_i then "Input " ++ toString j.val ++ " has higher ROI"
  else "Equal ROI"

/-- Output elasticity of input i (already stored as αᵢ) -/
def inputElasticity {n : ℕ} (cd : CobbDouglasMatrix n) (i : Fin n) : ℝ := cd.α i

/-- Get elasticity for specific input -/
def getElasticity {n : ℕ} (cd : CobbDouglasMatrix n) (i : Fin n) : ℝ :=
  cd.α i

/-- Optimal input allocation given price vector -/
noncomputable def optimalAllocation {n : ℕ} (cd : CobbDouglasMatrix n) (prices : Fin n → ℝ) 
  (budget : ℝ) : Fin n → ℝ :=
  λ i => if prices i > 0 then (cd.α i / (returnsToScale cd)) * budget / prices i else 0

/-- Compare three key metrics for investment decisions -/
noncomputable def investmentAnalysis {n : ℕ} (cd : CobbDouglasMatrix n) (i : Fin n) : ℝ × ℝ × ℝ :=
  (marginalProduct cd i, roiInput cd i, cd.α i)

/-- Check if production exhibits constant, increasing, or decreasing returns -/
noncomputable def scaleType {n : ℕ} (cd : CobbDouglasMatrix n) : String :=
  let rts := returnsToScale cd
  if rts = 1 then "Constant returns to scale"
  else if rts > 1 then "Increasing returns to scale" 
  else "Decreasing returns to scale"

/-- Example: 3-input Cobb–Douglas (K, L, K_AI) -/
noncomputable def exampleCD : CobbDouglasMatrix 3 :=
  { A := 1.2,
    α := ![0.4, 0.4, 0.2],   -- α, β, γ
    x := ![100, 50, 10],     -- K, L, K_AI
    hA := by norm_num,
    hα := by intro i; fin_cases i <;> norm_num,
    hx := by intro i; fin_cases i <;> norm_num }

#check output exampleCD     -- check type
#check returnsToScale exampleCD
#check marginalProduct exampleCD 2  -- marginal productivity of AI capital
#check investmentAnalysis exampleCD 0  -- analysis for first input

end Econ