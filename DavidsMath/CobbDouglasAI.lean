-- CobbDouglasAI.lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Econ

/-- Cobb–Douglas production function -/
structure CobbDouglas where
  A : ℝ
  K : ℝ
  L : ℝ
  α : ℝ
  β : ℝ
  hA : A > 0        -- total factor productivity strictly positive
  hK : K ≥ 0        -- capital non-negative
  hL : L ≥ 0        -- labor non-negative
  hα : α > 0        -- capital elasticity positive
  hβ : β > 0        -- labor elasticity positive

/-- Output function Y = A * K^α * L^β -/
noncomputable def output (cd : CobbDouglas) : ℝ :=
  cd.A * (cd.K ^ cd.α) * (cd.L ^ cd.β)

/-- Marginal productivity of capital ∂Y/∂K -/
noncomputable def MPK (cd : CobbDouglas) : ℝ :=
  cd.A * cd.α * (cd.K ^ (cd.α - 1)) * (cd.L ^ cd.β)

/-- Marginal productivity of labor ∂Y/∂L -/
noncomputable def MPL (cd : CobbDouglas) : ℝ :=
  cd.A * cd.β * (cd.K ^ cd.α) * (cd.L ^ (cd.β - 1))

/-- Returns to scale property -/
noncomputable def returnsToScale (cd : CobbDouglas) : String :=
  if cd.α + cd.β = 1 then "Constant returns to scale"
  else if cd.α + cd.β > 1 then "Increasing returns to scale"
  else "Decreasing returns to scale"

/-- Return on Investment (ROI) for capital: MPK/K -/
noncomputable def roiCapital (cd : CobbDouglas) : ℝ :=
  if cd.K > 0 then (MPK cd) / cd.K else 0

/-- Return on Investment (ROI) for labor: MPL/L -/
noncomputable def roiLabor (cd : CobbDouglas) : ℝ :=
  if cd.L > 0 then (MPL cd) / cd.L else 0

/-- Compare which input has higher marginal productivity -/
noncomputable def higherMarginalProduct (cd : CobbDouglas) : String :=
  if MPK cd > MPL cd then "Capital has higher marginal product"
  else if MPL cd > MPK cd then "Labor has higher marginal product"
  else "Equal marginal products"

/-- Compare which input has higher ROI -/
noncomputable def higherROI (cd : CobbDouglas) : String :=
  if roiCapital cd > roiLabor cd then "Capital has higher ROI"
  else if roiLabor cd > roiCapital cd then "Labor has higher ROI"
  else "Equal ROI"

/-- Output elasticity of capital (percentage change in output for 1% change in capital) -/
def capitalElasticity (cd : CobbDouglas) : ℝ := cd.α

/-- Output elasticity of labor (percentage change in output for 1% change in labor) -/
def laborElasticity (cd : CobbDouglas) : ℝ := cd.β

/-- Which input is more elastic (responsive) -/
noncomputable def moreElastic (cd : CobbDouglas) : String :=
  if cd.α > cd.β then "Output more elastic to capital changes"
  else if cd.β > cd.α then "Output more elastic to labor changes"
  else "Equal elasticity"

/-- Optimal capital-labor ratio (when MPK/MPL equals input price ratio) -/
noncomputable def optimalCapitalLaborRatio (cd : CobbDouglas) (priceCapital priceLabor : ℝ) : ℝ :=
  if priceLabor > 0 ∧ cd.L > 0 ∧ cd.β > 0 then
    (cd.α / cd.β) * (priceLabor / priceCapital) * (cd.L / cd.K)
  else 0

end Econ

