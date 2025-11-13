import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

-- Discounted Cash Flow Analysis in Lean
namespace DCF

-- Basic types for our DCF model
structure CashFlow where
  period : ℕ
  amount : ℝ

-- Financial statement components for FCF calculation
structure FinancialData where
  revenue : ℝ
  operating_expenses : ℝ
  depreciation : ℝ
  ebit : ℝ
  tax_rate : ℝ
  capex : ℝ
  change_in_working_capital : ℝ

-- Capital structure for WACC calculation
structure CapitalStructure where
  market_value_equity : ℝ
  market_value_debt : ℝ
  cost_of_equity : ℝ
  cost_of_debt : ℝ
  tax_rate : ℝ

-- Discount rate and terminal value
structure DCFParameters where
  discount_rate : ℝ
  terminal_growth_rate : ℝ
  terminal_value : ℝ

-- WACC (Weighted Average Cost of Capital) calculation
def wacc (cs : CapitalStructure) : ℝ :=
  let total_value := cs.market_value_equity + cs.market_value_debt
  let equity_weight := cs.market_value_equity / total_value
  let debt_weight := cs.market_value_debt / total_value
  let after_tax_cost_debt := cs.cost_of_debt * (1 - cs.tax_rate)
  equity_weight * cs.cost_of_equity + debt_weight * after_tax_cost_debt

-- Free Cash Flow calculation
def free_cash_flow (fd : FinancialData) : ℝ :=
  let nopat := fd.ebit * (1 - fd.tax_rate)  -- Net Operating Profit After Tax
  nopat + fd.depreciation - fd.capex - fd.change_in_working_capital

-- EBIT calculation from revenue and expenses
def calculate_ebit (revenue : ℝ) (operating_expenses : ℝ) (depreciation : ℝ) : ℝ :=
  revenue - operating_expenses - depreciation

-- Present value of a single cash flow
def present_value (cf : CashFlow) (discount_rate : ℝ) : ℝ :=
  cf.amount / (1 + discount_rate) ^ cf.period

-- Present value of a list of cash flows
def npv (cash_flows : List CashFlow) (discount_rate : ℝ) : ℝ :=
  cash_flows.map (fun cf => present_value cf discount_rate) |>.sum

-- Terminal value calculation (Gordon Growth Model)
def terminal_value (final_cf : ℝ) (growth_rate : ℝ) (discount_rate : ℝ) : ℝ :=
  (final_cf * (1 + growth_rate)) / (discount_rate - growth_rate)

-- Project FCF for multiple years with growth rates
def project_fcf (base_fcf : ℝ) (growth_rates : List ℝ) : List ℝ :=
  growth_rates.scanl (fun acc rate => acc * (1 + rate)) base_fcf |>.tail!

-- Convert FCF projections to CashFlow list
def fcf_to_cashflows (fcf_projections : List ℝ) : List CashFlow :=
  fcf_projections.enum.map (fun ⟨i, fcf⟩ => ⟨i + 1, fcf⟩)

-- Complete DCF valuation using WACC
def dcf_valuation_wacc (fcf_projections : List ℝ) (wacc_rate : ℝ) 
  (terminal_growth : ℝ) : ℝ :=
  let cash_flows := fcf_to_cashflows fcf_projections
  let operating_pv := npv cash_flows wacc_rate
  let final_fcf := fcf_projections.getLast!
  let terminal_val := terminal_value final_fcf terminal_growth wacc_rate
  let terminal_pv := terminal_val / (1 + wacc_rate) ^ fcf_projections.length
  operating_pv + terminal_pv

-- Complete DCF valuation (original)
def dcf_valuation (operating_cf : List CashFlow) (params : DCFParameters) : ℝ :=
  let operating_pv := npv operating_cf params.discount_rate
  let terminal_pv := params.terminal_value / (1 + params.discount_rate) ^ operating_cf.length
  operating_pv + terminal_pv

-- Theorems about DCF properties
theorem present_value_decreases_with_time (amount : ℝ) (discount_rate : ℝ) 
  (h1 : amount > 0) (h2 : discount_rate > 0) (n m : ℕ) (h3 : n < m) :
  present_value ⟨m, amount⟩ discount_rate < present_value ⟨n, amount⟩ discount_rate := by
  simp [present_value]
  apply div_lt_div_of_lt_left h1
  · apply pow_pos
    linarith
  · apply pow_lt_pow_right
    linarith
    exact h3

theorem npv_additive (cf1 cf2 : List CashFlow) (discount_rate : ℝ) :
  npv (cf1 ++ cf2) discount_rate = npv cf1 discount_rate + npv cf2 discount_rate := by
  simp [npv, List.map_append, List.sum_append]

theorem wacc_bounded (cs : CapitalStructure) 
  (h1 : cs.market_value_equity > 0) (h2 : cs.market_value_debt > 0)
  (h3 : cs.cost_of_equity ≥ 0) (h4 : cs.cost_of_debt ≥ 0) (h5 : 0 ≤ cs.tax_rate ∧ cs.tax_rate < 1) :
  0 ≤ wacc cs ∧ wacc cs ≤ max cs.cost_of_equity cs.cost_of_debt := by
  sorry -- Proof sketch: WACC is weighted average, so bounded by min/max of components

theorem fcf_consistent_with_ebit (fd : FinancialData) :
  free_cash_flow fd = fd.ebit * (1 - fd.tax_rate) + fd.depreciation - fd.capex - fd.change_in_working_capital := by
  simp [free_cash_flow]

-- Example company financial data
def example_company : FinancialData := {
  revenue := 10000,
  operating_expenses := 6000,
  depreciation := 500,
  ebit := 3500,  -- Revenue - OpEx - Depreciation
  tax_rate := 0.25,
  capex := 800,
  change_in_working_capital := 200
}

-- Example capital structure
def example_capital_structure : CapitalStructure := {
  market_value_equity := 50000,
  market_value_debt := 20000,
  cost_of_equity := 0.12,  -- 12%
  cost_of_debt := 0.06,    -- 6%
  tax_rate := 0.25         -- 25%
}

-- Comprehensive DCF example using WACC and FCF projections
def comprehensive_dcf_example : ℝ :=
  -- Calculate base year FCF
  let base_fcf := free_cash_flow example_company
  -- Project FCF for 5 years with varying growth rates
  let growth_rates := [0.15, 0.12, 0.10, 0.08, 0.05]  -- Declining growth
  let fcf_projections := project_fcf base_fcf growth_rates
  -- Calculate WACC
  let company_wacc := wacc example_capital_structure
  -- Terminal growth rate
  let terminal_growth := 0.03
  -- Calculate enterprise value
  dcf_valuation_wacc fcf_projections company_wacc terminal_growth

-- Example DCF calculation (original simple version)
def example_dcf : ℝ :=
  let cash_flows : List CashFlow := [
    ⟨1, 1000⟩,  -- Year 1: $1000
    ⟨2, 1100⟩,  -- Year 2: $1100
    ⟨3, 1210⟩,  -- Year 3: $1210
    ⟨4, 1331⟩,  -- Year 4: $1331
    ⟨5, 1464⟩   -- Year 5: $1464
  ]
  let params : DCFParameters := {
    discount_rate := 0.1,      -- 10% discount rate
    terminal_growth_rate := 0.03, -- 3% terminal growth
    terminal_value := terminal_value 1464 0.03 0.1
  }
  dcf_valuation cash_flows params

-- Scenario analysis for DCF
structure Scenario where
  name : String
  fcf_growth_rates : List ℝ
  terminal_growth : ℝ
  wacc_adjustment : ℝ  -- Adjustment to base WACC

def scenario_analysis (base_fcf : ℝ) (base_wacc : ℝ) (scenarios : List Scenario) : List (String × ℝ) :=
  scenarios.map (fun s => 
    let fcf_proj := project_fcf base_fcf s.fcf_growth_rates
    let adjusted_wacc := base_wacc + s.wacc_adjustment
    let valuation := dcf_valuation_wacc fcf_proj adjusted_wacc s.terminal_growth
    (s.name, valuation))

-- Calculate debt-to-equity ratio
def debt_to_equity_ratio (cs : CapitalStructure) : ℝ :=
  cs.market_value_debt / cs.market_value_equity

-- Calculate return on invested capital (ROIC) approximation
def roic (fd : FinancialData) (invested_capital : ℝ) : ℝ :=
  let nopat := fd.ebit * (1 - fd.tax_rate)
  nopat / invested_capital

-- Sensitivity analysis helper (enhanced)
def sensitivity_analysis (base_cf : List CashFlow) (base_rate : ℝ) 
  (rate_variations : List ℝ) : List (ℝ × ℝ) :=
  rate_variations.map (fun r => (r, npv base_cf r))

-- FCF sensitivity to growth assumptions
def fcf_sensitivity (base_fcf : ℝ) (base_growth : List ℝ) 
  (growth_adjustments : List ℝ) : List (ℝ × ℝ) :=
  growth_adjustments.map (fun adj => 
    let adjusted_growth := base_growth.map (fun g => g + adj)
    let fcf_proj := project_fcf base_fcf adjusted_growth
    (adj, fcf_proj.sum))

end DCF