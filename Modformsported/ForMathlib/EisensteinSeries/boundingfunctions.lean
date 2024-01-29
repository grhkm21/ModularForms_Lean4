import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.Modular
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Modformsported.ForMathlib.EisensteinSeries.bounds
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Modformsported.ForMathlib.EisensteinSeries.lattice_functions
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.Series

noncomputable section

open Complex Filter UpperHalfPlane Set

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane Complex

namespace EisensteinSeries

/-- Auxilary function used for bounding Eisentein series-/
def lowerBound1 (z : ℍ) : ℝ :=
  ((z.1.2 ^ (2 : ℕ)) / (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)))

theorem lowerBound1_pos (z : ℍ) : 0 < lowerBound1 z := by
  rw [lowerBound1]
  have H1 := upper_half_im_pow_pos z 2
  have H2 : 0 < (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ))  := by
    norm_cast
    apply_rules [pow_pos, add_pos_of_nonneg_of_pos, pow_two_nonneg]
  have := div_pos H1 H2
  norm_cast at *

/-- This function is used to give an upper bound on Eisenstein series-/
def r (z : ℍ) : ℝ :=
  min (z.1.2) (Real.sqrt (lowerBound1 z))

theorem r_pos (z : ℍ) : 0 < r z :=
  by
  have H := z.property; simp at H
  rw [r]
  simp only [lt_min_iff, Real.sqrt_pos, UpperHalfPlane.coe_im]
  constructor
  have := upper_half_im_pow_pos z 2
  norm_cast at *
  apply lowerBound1_pos

theorem r_ne_zero (z : ℍ) :  r z ≠ 0 := ne_of_gt (r_pos z)

lemma r_mul_n_pos (k : ℕ) (z : ℍ) (n : ℕ)  (hn : 1 ≤ n) :
  0 < (Complex.abs ((r z : ℂ) ^ (k : ℤ) * (n : ℂ)^ (k : ℤ))) := by
  apply Complex.abs.pos
  apply mul_ne_zero
  norm_cast
  apply pow_ne_zero
  apply r_ne_zero
  norm_cast
  apply pow_ne_zero
  linarith

lemma pow_two_of_nonzero_ge_one (a : ℤ) (ha : a  ≠ 0) : 0 ≤ a^2 - 1  := by
  simp only [sub_nonneg, one_le_sq_iff_one_le_abs, ge_iff_le]
  exact Int.one_le_abs ha

theorem auxlb (z : ℍ) (δ : ℝ) (n : ℤ) (hn : n ≠ 0) :
    (z.1.2 ^ 2 ) / (z.1.1 ^ 2 + z.1.2 ^ 2) ≤  (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 := by
  have H1 : (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 =
        δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + n * 2 * δ * z.1.1 + n^2 := by
    ring
  have H4 :
    (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + n * 2 * δ * z.1.1   + n^2) * (z.1.1 ^ 2 + z.1.2 ^ 2) -
      (z.1.2 ^ 2) =
    (δ * (z.1.1 ^ 2 + z.1.2 ^ 2)+ n * z.1.1)^2 + (n^2-1)* (z.1.2)^2 := by
     ring
  rw [H1, div_le_iff, ← sub_nonneg, H4]
  · apply add_nonneg
    apply pow_two_nonneg
    apply mul_nonneg
    norm_cast
    apply pow_two_of_nonzero_ge_one n hn
    apply pow_two_nonneg
  · apply_rules [add_pos_of_nonneg_of_pos, pow_two_nonneg, upper_half_im_pow_pos z 2]

theorem auxbound1 (z : ℍ) (δ : ℝ) : r z ≤ Complex.abs ((z : ℂ) + δ)  := by
    rw [r, Complex.abs]
    have H1 :
      (z : ℂ).im ≤ Real.sqrt (((z : ℂ).re + δ) * ((z : ℂ).re + δ) + (z : ℂ).im * (z : ℂ).im) := by
      rw [Real.le_sqrt' ]
      norm_cast
      nlinarith
      apply z.2
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, AbsoluteValue.coe_mk, MulHom.coe_mk,
      min_le_iff] at *
    left
    norm_cast
    rw [normSq_apply]
    simp only [add_re, UpperHalfPlane.coe_re, ofReal_re, add_im, UpperHalfPlane.coe_im, ofReal_im,
      add_zero]
    norm_cast at *

theorem auxbound2 (z : ℍ) (δ : ℝ) (n : ℤ) (h : n ≠ 0) : r z ≤ Complex.abs (δ * (z : ℂ) + n) := by
  rw [r, Complex.abs]
  have H1 :
    Real.sqrt (lowerBound1 z) ≤
      Real.sqrt
        ((δ * (z : ℂ).re + n) * (δ * (z : ℂ).re + n) + δ * (z : ℂ).im * (δ * (z : ℂ).im)) :=
    by
    rw [lowerBound1, Real.sqrt_le_sqrt_iff, ← pow_two, ← pow_two]
    have := auxlb z δ n h
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at *
    norm_cast at *
    nlinarith
  simp only [ne_eq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, AbsoluteValue.coe_mk,
    MulHom.coe_mk, min_le_iff] at *
  rw [normSq_apply]
  right
  simp only [add_re, mul_re, ofReal_re, UpperHalfPlane.coe_re, ofReal_im, UpperHalfPlane.coe_im,
    zero_mul, sub_zero, int_cast_re, add_im, mul_im, add_zero, int_cast_im] at *
  norm_cast

/-
theorem baux_ (a : ℝ) (k : ℤ) (hk : 0 ≤ k) (b : ℂ) (h : 0 ≤ a) (h2 : a ≤ Complex.abs b) :
    a ^ k ≤ Complex.abs (b ^ k) := by
  lift k to ℕ using hk
  norm_cast at *
  simp only [Complex.cpow_int_cast, map_pow]
  norm_cast at *
  apply pow_le_pow_left h h2
  -/

theorem abs_zpow_r_eq_r (z : ℍ) (k : ℤ) : Complex.abs (r z ^ k) = r z ^ k := by
  have ha := (r_pos z).le
  have := Complex.abs_of_nonneg ha
  rw [←this]
  simp  [abs_ofReal, cpow_nat_cast, map_pow, _root_.abs_abs, Real.rpow_nat_cast]

theorem bound1 (z : ℍ) (x : Fin 2 → ℤ) (k : ℤ) (hk : 0 ≤ k) :
    Complex.abs ((r z : ℂ) ^ k) ≤ Complex.abs (((z : ℂ) + (x 1 : ℂ) / (x 0 : ℂ)) ^ k) := by
  have H1 : Complex.abs (r z ^ k) = r z ^ k := by apply abs_zpow_r_eq_r
  norm_cast at *
  rw [H1]
  have := auxbound1 z (x 1 / x 0 : ℝ)
  lift k to ℕ using hk
  simp only [zpow_coe_nat, map_pow, ge_iff_le]
  apply pow_le_pow_left (r_pos _).le
  simp only [ofReal_div, ofReal_int_cast, zpow_coe_nat, _root_.abs_pow, ge_iff_le, abs_nonneg] at *
  convert this
  norm_cast

theorem bound2 (z : ℍ) (x : Fin 2 → ℤ) (k : ℤ) (hk : 0 ≤ k) :
    Complex.abs ((r z : ℂ) ^ k) ≤ Complex.abs (((x 0 : ℂ) / (x 1 : ℂ) * (z : ℂ) + 1) ^ k) := by
  have H1 : Complex.abs (r z ^ k) = r z ^ k := by apply abs_zpow_r_eq_r
  norm_cast at *
  rw [H1]
  have := auxbound2 z (x 0 / x 1 : ℝ) 1 one_ne_zero
  lift k to ℕ using hk
  simp only [zpow_coe_nat, map_pow, ge_iff_le]
  apply pow_le_pow_left (r_pos _).le
  simp only [ofReal_div, ofReal_int_cast, Int.cast_one, zpow_coe_nat, _root_.abs_pow, ge_iff_le,
    abs_nonneg] at *
  convert this
  norm_cast

def upperHalfPlaneSlice (A B : ℝ) :=
  {z : ℍ | Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B}

theorem slice_mem (A B : ℝ) (z : ℍ) :
    z ∈ upperHalfPlaneSlice A B ↔ Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B :=
  Iff.rfl

lemma compact_in_some_slice (K : Set ℍ) (hK : IsCompact K) : ∃  A B : ℝ, 0 < B ∧
    K ⊆ upperHalfPlaneSlice A B  := by
  by_cases hne : Set.Nonempty K
  have hcts : ContinuousOn (fun t =>  t.im) K := by
    apply Continuous.continuousOn
    apply UpperHalfPlane.continuous_im
  have := IsCompact.exists_isMinOn hK hne hcts
  obtain ⟨b, _, HB⟩ := this
  let t := (⟨Complex.I, by simp⟩ : ℍ)
  have  ht : UpperHalfPlane.im t = I.im := by rfl
  have hb2 := Bornology.IsBounded.subset_closedBall_lt hK.isBounded 0 t
  obtain ⟨r, hr, hr2⟩ := hb2
  refine' ⟨Real.sinh (r) + Complex.abs ((UpperHalfPlane.center t r)), b.im, _⟩
  constructor
  apply b.2
  intro z hz
  simp  [slice_mem, coe_re, coe_im, ge_iff_le, Set.top_eq_univ,
    Set.image_univ, range_inclusion] at *
  constructor
  have hr3 := hr2 hz
  simp  at hr3
  norm_cast at *
  apply le_trans (abs_re_le_abs z)
  have := Complex.abs.sub_le (z : ℂ) (UpperHalfPlane.center t r) 0
  simp  [sub_zero, Subtype.coe_mk, abs_I] at this
  rw [dist_le_iff_dist_coe_center_le] at hr3
  simp at *
  apply le_trans this
  simp
  have htim : UpperHalfPlane.im t = 1 := by
     simp [ht]
  rw [htim] at hr3
  simp at hr3
  apply hr3
  have hbz := HB  hz
  simp at *
  convert hbz
  rw [UpperHalfPlane.im]
  apply abs_eq_self.mpr z.2.le
  rw [not_nonempty_iff_eq_empty] at hne
  rw [hne]
  simp
  use 1
  linarith

def lbpoint (A B : ℝ) (h : 0 < B) : ℍ :=
  ⟨⟨A, B⟩, by simp [h]⟩

theorem aux4 (a b : ℝ) (h : 0 < b) :
    (b ^ 2) / (a ^ 2 + b ^ 2) = 1 / ((a / b) ^ 2 + 1) :=
  by
  field_simp


@[simp]
lemma uhc (z : ℍ) : (z : ℂ) = z.1 := by rfl

theorem rfunct_lower_bound_on_slice (A B : ℝ) (h : 0 < B) (z : upperHalfPlaneSlice A B) :
    r (lbpoint A B h) ≤ r z.1 := by
  simp_rw [lbpoint]
  have zpos := UpperHalfPlane.im_pos z.1
  have hz := z.2
  rw [slice_mem] at hz
  simp only [abs_ofReal, ge_iff_le] at hz
  rw [r, r]
  apply min_le_min
  · dsimp only
    convert hz.2
    have := abs_eq_self.mpr zpos.le
    convert this.symm
  rw [Real.sqrt_le_sqrt_iff]
  have := aux4 (z : ℂ).re (z : ℂ).im zpos
  simp only [uhc, div_pow, one_div] at this
  simp_rw [lowerBound1]
  rw [this, aux4 A B h, one_div, inv_le_inv, add_le_add_iff_right, div_pow]
  apply div_le_div (sq_nonneg _)
  · simpa [even_two.pow_abs] using pow_le_pow_left (abs_nonneg _) hz.1 2
  · positivity
  · simpa [even_two.pow_abs] using pow_le_pow_left h.le hz.2 2
  · positivity
  · positivity
  · apply (lowerBound1_pos z).le


variable {α : Type u} {β : Type v} {γ : Type w} {i : α → Set β}

def unionEquiv (ι : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : (Fin 2 → ℤ), ∃! i : ℕ, ⟨y 0, y 1⟩ ∈ ι i) :
    (⋃ s : ℕ, ((ι s) : Set (ℤ × ℤ))) ≃ (ℤ × ℤ) where
  toFun x := x.1
  invFun x := by
    use x
    simp
    obtain ⟨i, hi1,_⟩:= HI ![x.1, x.2]
    refine ⟨i,hi1⟩
  left_inv := by  intro x; cases x; rfl
  right_inv := by intro x; rfl

theorem summable_disjoint_union_of_nonneg {i : α → Set β} {f : (⋃ x, i x) → ℝ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔
      (∀ x, Summable fun y : i x => f ⟨y,  Set.mem_iUnion_of_mem (x) y.2 ⟩) ∧
        Summable fun x => ∑' y : i x, f ⟨y, Set.mem_iUnion_of_mem (x) y.2 ⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h01 : Summable f ↔ Summable (f ∘ h0) := by
   rw [Equiv.summable_iff]
  have h22 : ∀ y : Σ s : α, i s, 0 ≤ (f ∘ h0) y :=
    by
    intro y
    simp
    apply hf
  have h1 := summable_sigma_of_nonneg h22
  rw [←h01] at h1;
  convert h1

theorem tsum_disjoint_union_of_nonneg' {γ : Type} [AddCommGroup γ]  [ UniformSpace γ]
    [UniformAddGroup γ] [CompleteSpace γ] [T0Space γ] [T2Space γ]
    {i : α → Set β} {f : (⋃ x, i x) → γ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (h1 : Summable f) :
    ∑' x, f x = ∑' x, ∑' y : i x, f ⟨y, Set.mem_iUnion_of_mem (x) y.2⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h11 : ∑' x, f x = ∑' y, f (h0 y) := by have := Equiv.tsum_eq h0 f; rw [← this]
  rw [h11]
  rw [tsum_sigma]
  rfl
  have h01 : Summable f ↔ Summable (f ∘ h0) := by rw [Equiv.summable_iff]
  convert (h01.1 h1)

theorem disjoint_aux (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : (Fin 2 → ℤ), ∃! i : ℕ, ⟨y 0, y 1⟩ ∈ In i) :
    ∀ i j : ℕ, i ≠ j → Disjoint (In i) (In j) :=
  by
  intro i j h
  intro x h1 h2 a h3
  have H0 := HI ![a.1, a.2]
  have := ExistsUnique.unique H0 (h1 h3) (h2 h3)
  simp at *
  exact h this

lemma vsdv (g : ℤ × ℤ → ℝ) (v : Finset (ℤ × ℤ)) : Summable fun (x : v) => g x := by
  apply Finset.summable


theorem sum_lemma (f : (Fin 2 → ℤ) → ℝ)  (h : ∀ y : (Fin 2 → ℤ), 0 ≤ f y) (ι : ℕ → Finset (ℤ × ℤ))
    (HI : ∀ y : (Fin 2 → ℤ), ∃! i : ℕ, ⟨y 0, y 1⟩ ∈ ι i) :
    Summable f ↔ Summable fun n : ℕ => ∑ x in ι n, f ![x.1, x.2] :=
  by
  let h2 := Equiv.trans (unionEquiv ι HI) (piFinTwoEquiv fun _ => ℤ).symm
  have h22 : ∀ y : ⋃ s : ℕ, (ι s), 0 ≤ (f ∘ h2) y :=
    by
    intro y
    apply h
  have hdis' := disjoint_aux ι HI
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint ((ι a)) ((ι b)) :=
    by
    intro a b hab;
    apply hdis'; exact hab
  have h3 := summable_disjoint_union_of_nonneg ?_ h22
  have h4 : Summable f ↔ Summable (f ∘ h2) := by rw [Equiv.summable_iff]
  rw [h4]
  rw [h3]
  constructor
  intro H
  convert H.2
  rw [←Finset.tsum_subtype]
  rfl
  intro H
  constructor
  intro x

  simp only [Finset.coe_sort_coe, Equiv.coe_trans, Function.comp_apply]
  rw [unionEquiv]
  simp only [Equiv.coe_fn_mk]
  convert (Finset.summable (ι x) (f ∘ (piFinTwoEquiv fun _ => ℤ).symm))
  convert H
  rw [←Finset.tsum_subtype]
  rfl
  norm_cast

lemma summable_rfunct_twist  (k : ℤ) (z : ℍ) (h : 3 ≤ k) :
  Summable fun n : ℕ => 8 / (r z) ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ := by
  have hk : 1 < (k - 1 : ℝ) := by
    have : 1 < (k -1  : ℤ) := by linarith
    norm_cast at *
  have riesum := Real.summable_nat_rpow_inv.2 hk
  have nze : (8 / (r z) ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp only [Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero]
    linarith
    norm_cast
    apply zpow_ne_zero
    simp only [Ne.def]
    by_contra HR
    have := r_pos z
    rw [HR] at this
    simp only [lt_self_iff_false] at this
  rw [← (summable_mul_left_iff nze).symm]
  simp only [Int.cast_ofNat, Int.cast_one, Int.cast_sub] at riesum
  convert riesum
  norm_cast

lemma summable_upper_bound (k : ℤ) (h : 3 ≤ k) (z : ℍ) :
 Summable fun (x : Fin 2 → ℤ) =>
  (1/((r z)^k))*((max (x 0).natAbs (x 1).natAbs : ℝ)^k)⁻¹ := by
  rw [sum_lemma _ _ (fun (n : ℕ) => square n)]
  have : ∀ n : ℕ, ∑ v in square n, (1/((r z)^k))*((max v.1.natAbs v.2.natAbs: ℝ)^k)⁻¹ =
     ∑ v in square n, (1/(r (z)^k))*((n : ℝ)^k)⁻¹ := by
     intro n
     apply Finset.sum_congr
     rfl
     intro x hx
     simp at hx
     congr
     norm_cast at *
  have hs : Summable (fun n : ℕ => ∑ v in square n, (1/((r z)^k))*((n : ℝ)^k)⁻¹ )  := by
    simp
    apply Summable.congr (summable_rfunct_twist k z h)
    intro b
    by_cases b0 : b = 0
    rw [b0]
    have hk : (0: ℝ)^((k : ℤ)-1) = 0:= by
      rw [zero_zpow]
      linarith
    simp at *
    rw [hk]
    simp
    right
    have hk0 : 0 ≤ k := by linarith
    lift k to ℕ using hk0
    simp  [zpow_coe_nat, ne_eq, zero_pow_eq_zero, gt_iff_lt]
    right
    linarith
    rw [square_size' b0]
    field_simp
    ring_nf
    simp_rw [mul_assoc]
    have hbb : (b : ℝ)^(-1 + (k : ℝ)) = (b : ℝ)⁻¹ * b^(k : ℝ) := by
      rw [Real.rpow_add]
      congr
      exact Real.rpow_neg_one ↑b
      simpa [pos_iff_ne_zero] using b0
    norm_cast at *
    rw [hbb]
    ring_nf
    simp
  apply Summable.congr hs
  intro b
  apply (this b).symm
  apply squares_cover_all'
  intro y
  apply mul_nonneg
  simp
  apply zpow_nonneg
  apply (r_pos z).le
  simp  [ge_iff_le, Nat.cast_le, Real.rpow_nat_cast, inv_nonneg, le_max_iff, Nat.cast_nonneg,
    or_self, zpow_nonneg]

theorem Eise_on_square_is_bounded2 (k : ℤ) (hk : 0 ≤ k) (z : ℍ) (n : ℕ) (hn : 1 ≤ k) :
    ∀ x : Fin 2 → ℤ,
      ⟨x 0, x 1⟩ ∈ square n →
        (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs ((r z) ^ k * n ^ k))⁻¹ :=
  by
  sorry

theorem r_abs_pos (z : ℍ) : 0 < |r z| :=
  by
  simpa using (r_ne_zero z)

lemma  Eisenstein_lvl_N_tendstolocunif_22  (k : ℤ) (hk : 3 ≤ k) (N : ℕ) (a : Fin 2 → ZMod N) :
  TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) =>
    (fun (z : ℍ) => ∑ x in s, eisSummand k x z ) )
    ( fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) Filter.atTop ⊤ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  --intro K hK hK2
  rw [eisensteinSeries_SIF]

  simp [eisensteinSeries]
  intros K hK
  obtain ⟨A,B,hB, HABK⟩:= compact_in_some_slice K hK
  let u :=  fun x : (gammaSet N a )  =>
    (1/((r (lbpoint A B hB))^k))* ( (max (x.1 0).natAbs (x.1 1).natAbs : ℝ)^k)⁻¹
  have hu : Summable u := by
    have := summable_upper_bound k hk (lbpoint A B hB)
    simp at this
    have := Summable.subtype this (gammaSet N a )
    apply this.congr
    intro v
    simp
  apply tendstoUniformlyOn_tsum hu
  intro v x hx
  have hkgt1 : 1 ≤ k := by linarith
  have sq := square_mem (max (((piFinTwoEquiv fun _ => ℤ).1 v).1).natAbs
  (((piFinTwoEquiv fun _ => ℤ).1 v).2).natAbs ) ⟨(v.1 0), v.1 1⟩
  simp at sq
  have hk0 : 0 ≤ k := by linarith
  have := Eise_on_square_is_bounded2 k hk0 x (max (v.1 0).natAbs (v.1 1).natAbs ) hkgt1 v
  simp  at this
  rw [eisSummand]
  simp
  apply le_trans (this sq)
  rw [mul_comm]
  apply mul_le_mul
  rw [inv_le_inv]
  lift k to ℕ using hk0
  apply pow_le_pow_left
  apply (r_pos _).le
  rw [abs_of_pos (r_pos _)]
  exact rfunct_lower_bound_on_slice A B hB ⟨x, HABK hx⟩
  lift k to ℕ using hk0
  apply pow_pos (r_abs_pos _)
  lift k to ℕ using hk0
  apply pow_pos (r_pos _)
  rfl
  simp only [ge_iff_le, Nat.cast_le, inv_nonneg, le_max_iff, Nat.cast_nonneg, or_self, zpow_nonneg]
  simp only [inv_nonneg, ge_iff_le]
  apply zpow_nonneg (r_pos _).le
  simp only [top_eq_univ, isOpen_univ]
