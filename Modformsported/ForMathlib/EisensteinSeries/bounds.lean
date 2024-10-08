import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

noncomputable section

open Complex

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane Complex

lemma upper_half_im_pow_pos (z : ℍ) (n : ℕ) : 0 < z.im ^ n := pow_pos z.im_pos n

namespace EisensteinSeries

/-- Auxilary function used for bounding Eisentein series-/
def lb (z : ℍ) : ℝ :=
  ((z.1.2 ^ (4 : ℕ) + (z.1.1 * z.1.2) ^ (2 : ℕ)) / (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)) ^ (2 : ℕ))

theorem lb_pos (z : ℍ) : 0 < lb z := by
  rw [lb]
  have H1 : 0 < z.1.2 ^ (4 : ℕ) + (z.1.1 * z.1.2) ^ (2 : ℕ) :=
    by
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos
    have := pow_two_nonneg (z.1.1*z.1.2)
    simpa using this
    apply upper_half_im_pow_pos z 4
  have H2 : 0 < (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)) ^ (2 : ℕ) := by
    norm_cast
    apply pow_pos
    apply add_pos_of_nonneg_of_pos
    apply pow_two_nonneg
    have := upper_half_im_pow_pos z 2
    norm_cast at this
  norm_cast at *
  have := div_pos H1 H2
  norm_cast at *

/-- This function is used to give an upper bound on Eisenstein series-/
def rfunct (z : ℍ) : ℝ :=
  min (Real.sqrt (z.1.2 ^ (2))) (Real.sqrt (lb z))

theorem rfunct_pos (z : ℍ) : 0 < rfunct z :=
  by
  have H := z.property; simp at H
  rw [rfunct]
  simp only [lt_min_iff, Real.sqrt_pos, UpperHalfPlane.coe_im]
  constructor
  have := upper_half_im_pow_pos z 2
  norm_cast at *
  apply lb_pos

theorem rfunct_ne_zero (z : ℍ) :  rfunct z ≠ 0 := by
  by_contra h
  have := rfunct_pos z
  rw [h] at this
  norm_cast at *

lemma rfunct_mul_n_pos (k : ℕ) (z : ℍ) (n : ℕ)  (hn : 1 ≤ n) :
    0 < (Complex.abs ((rfunct z : ℂ) ^ (k : ℤ) * (n : ℂ)^ (k : ℤ))) := by
  have := rfunct_pos z
  apply Complex.abs.pos
  norm_cast
  positivity

theorem ineq1 (x y d : ℝ) : 0 ≤ d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 + 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 :=
  by
  have h1 :
    d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 + 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 =
      (d * (x ^ 2 + y ^ 2) + x) ^ 2 := by
        ring
  rw [h1]
  positivity

theorem lowbound (z : ℍ) (δ : ℝ) :
    (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) / (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 ≤
      (δ * z.1.1 + 1) ^ 2 + (δ * z.1.2) ^ 2 :=
  by
  have H1 :
    (δ * z.1.1 + 1) ^ 2 + (δ * z.1.2) ^ 2 = δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + 2 * δ * z.1.1 + 1 := by
      norm_cast
      ring
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H1
  rw [H1]
  rw [div_le_iff]
  swap
  · have H8 : 0 < z.1.2 ^ 2 := by
      have := upper_half_im_pow_pos z 2
      norm_cast at *
    positivity
  have H2 :
    (δ ^ 2 * ((z.1.1) ^ 2 + z.1.2 ^ 2) + 2 * δ * z.1.1 + 1) *
        (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 =
      δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 3 +
          2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
        (z.1.1^ 2 + z.1.2 ^ 2) ^ 2 := by
          norm_cast
          ring
  norm_cast at *
  simp at *
  rw [H2]
  rw [← sub_nonneg]
  have H4 :
    δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 3 +
            2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
          (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 -
        (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) =
      (z.1.1 ^ 2 + z.1.2 ^ 2) *
        (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
            2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) +
          z.1.1 ^ 2) :=by
          ring
  norm_cast at *
  rw [H4]
  have H5 :
    0 ≤
      δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
          2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) +
        z.1.1 ^ 2 :=
    by apply ineq1
  have H6 : 0 ≤ z.1.1 ^ 2 + z.1.2 ^ 2 := by
    norm_cast
    nlinarith
  have HH :=mul_nonneg H6 H5
  simp at *
  norm_cast at *

theorem auxlem (z : ℍ) (δ : ℝ) :
    rfunct z ≤ Complex.abs ((z : ℂ) + δ) ∧ rfunct z ≤ Complex.abs (δ * (z : ℂ) + 1) := by
  constructor
  · rw [rfunct]
    rw [Complex.abs]
    simp
    have H1 :
      Real.sqrt ((z : ℂ).im ^ 2) ≤
        Real.sqrt (((z : ℂ).re + δ) * ((z : ℂ).re + δ) + (z : ℂ).im * (z : ℂ).im) :=
      by
      rw [Real.sqrt_le_sqrt_iff]
      nlinarith; nlinarith
    simp at *
    left
    rw [normSq_apply]
    simp
    norm_cast at *
  · rw [rfunct]
    rw [Complex.abs]
    simp
    have H1 :
      Real.sqrt (lb z) ≤
        Real.sqrt
          ((δ * (z : ℂ).re + 1) * (δ * (z : ℂ).re + 1) + δ * (z : ℂ).im * (δ * (z : ℂ).im)) :=
      by
      rw [lb]
      rw [Real.sqrt_le_sqrt_iff]
      have := lowbound z δ
      rw [← pow_two]
      rw [← pow_two]
      simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at *
      norm_cast at *
      nlinarith
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H1
    rw [normSq_apply]
    right
    simp at *
    norm_cast

lemma sdf (a b : ℝ) (k : ℤ) (hk : 0 ≤ k) (ha : 0 ≤ a) (hab : a ≤ b) : a^k ≤ b^k := by
  lift k to ℕ using hk
  exact pow_le_pow_left ha hab k

theorem baux (a : ℝ) (k : ℤ) (hk : 0 ≤ k) (b : ℂ) (h : 0 ≤ a) (h2 : a ≤ Complex.abs b) :
    a ^ k ≤ Complex.abs (b ^ k) := by
  lift k to ℕ using hk
  norm_cast at *
  simp only [map_pow]
  apply pow_le_pow_left h h2

theorem baux2 (z : ℍ) (k : ℤ) : Complex.abs (rfunct z ^ k) = rfunct z ^ k := by
  have ha := (rfunct_pos z).le
  have := Complex.abs_of_nonneg ha
  rw [←this]
  simp  [abs_ofReal, map_pow, _root_.abs_abs]

theorem auxlem2 (z : ℍ) (x : ℤ × ℤ) (k : ℤ) (hk : 0 ≤ k) :
    Complex.abs ((rfunct z : ℂ) ^ k) ≤ Complex.abs (((z : ℂ) + (x.2 : ℂ) / (x.1 : ℂ)) ^ k) :=
  by
  norm_cast
  have H1 : Complex.abs (rfunct z ^ k) = rfunct z ^ k := by apply baux2
  norm_cast at H1
  rw [H1]
  have := auxlem z (x.2 / x.1 : ℝ)
  norm_cast at this
  have t2 := this.1
  lift k to ℕ using hk
  norm_cast at *
  simp only [map_pow]
  simp
  apply pow_le_pow_left (rfunct_pos _).le
  simp at *
  convert t2




theorem auxlem3 (z : ℍ) (x : ℤ × ℤ) (k : ℤ) (hk : 0 ≤ k) :
    Complex.abs ((rfunct z : ℂ) ^ k) ≤ Complex.abs (((x.1 : ℂ) / (x.2 : ℂ) * (z : ℂ) + 1) ^ k) :=
  by
  norm_cast
  have H1 : Complex.abs (rfunct z ^ k) = rfunct z ^ k := by apply baux2
  norm_cast at H1
  rw [H1]
  have := auxlem z (x.1 / x.2 : ℝ)
  norm_cast at this
  have t2 := this.2
  lift k to ℕ using hk
  norm_cast at *
  simp only [map_pow]
  simp
  norm_cast at *
  apply pow_le_pow_left (rfunct_pos _).le
  simp at *
  convert t2
