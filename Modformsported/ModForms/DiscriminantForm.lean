import Modformsported.ForMathlib.EisensteinSeries.ModularForm
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Modformsported.ModForms.Riemzeta
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries



noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex CongruenceSubgroup

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

-- def eisensteinSeries (k : ℤ) :=
--   if h : 3 ≤ k then EisensteinSeriesModularForm k h else 0

local notation "G[" k "]" => eisensteinSeries_MF (show 3 ≤ k by decide) (N := 1) 0

def eisenstein4 :=
  60 • G[4]

def eisenstein6 :=
  140 • G[6]

local notation "E₄" => eisenstein4

local notation "E₆" => eisenstein6

def E_4_cubed : ModularForm (Gamma 1) 12 := (E₄).mul ((E₄).mul E₄)

def E_6_sq : ModularForm (Gamma 1) 12 := (E₆).mul E₆

def discriminantForm : ModularForm (Gamma 1) 12 := E_4_cubed - 27 • E_6_sq

open scoped DirectSum BigOperators

local notation "ℍ" => UpperHalfPlane

example : CommRing (⨁ n : ℤ, ModularForm (Gamma 1) n) := by infer_instance

variable (v : ⨁ n : ℕ, ModularForm (Gamma 1) n)

def e4 :=
  DirectSum.of _ 4 eisenstein4

def e6 :=
  DirectSum.of _ 6 eisenstein6

theorem gmul_eq_mul {a b : ℤ} (f : ModularForm (Gamma 1) a) (g : ModularForm (Gamma 1) b) :
    GradedMonoid.GMul.mul f g = f.mul g := by rfl

def delta :=
  e4 ^ 3 - 27 * e6 ^ 2

theorem eqvs_of_defs : DirectSum.of _ 12 discriminantForm = delta := by
  rw [delta]
  rw [e4]
  rw [e6]
  rw [discriminantForm]
  simp [map_sub, map_nsmul, nsmul_eq_mul, algebraMap.coe_one]
  congr
  rw [pow_three]
  simp_rw [DirectSum.of_mul_of]
  simp_rw [gmul_eq_mul]
  congr
  rw [pow_two]
  simp_rw [DirectSum.of_mul_of]
  simp_rw [gmul_eq_mul]
  congr
