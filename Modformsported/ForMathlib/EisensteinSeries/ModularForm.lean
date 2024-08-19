/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.mdifferentiable
import Modformsported.ForMathlib.EisensteinSeries.bounded_at_infty
import Mathlib.Algebra.Field.Power
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

open Complex UpperHalfPlane

open scoped BigOperators NNReal Classical Filter UpperHalfPlane Manifold MatrixGroups

open ModularForm

open SlashInvariantForm

-- local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R
--
-- local notation "GL(" n ", " R ")" => Matrix.GeneralLinearGroup (Fin n) R

-- why is this not in Mathlib?
@[inherit_doc]
scoped[MatrixGroups] notation "GL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

noncomputable section

namespace EisensteinSeries

#check eisensteinSeries_MF
-- def EisensteinSeriesModularForm (k : ℤ) (hk : 3 ≤ k) : ModularForm ⊤ k where
--   toFun := (Eisenstein_SIF ⊤ k)
--   slash_action_eq' := by convert (Eisenstein_SIF ⊤ k).2
--   holo' := Eisenstein_series_is_mdiff k hk
--   bdd_at_infty' A :=  Eisenstein_series_is_bounded k hk A


/-The stuff below needs to be moved-/
lemma coeGLl (A: SL(2,ℤ)) : (A : GL(2,ℤ)) i j = A.1 i j := by
  norm_cast

lemma neg_moeb_eq_id (z : ℍ) : (-1 : SL(2,ℤ)) • z = z := by
  simp

#check slash_action_eqn'
-- theorem slash_action_eqn'' (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [SlashInvariantFormClass F Γ k] (f : F)
--     (γ : Γ) (z : ℍ) : f (γ • z) = ((γ.1 1 0 : ℂ) * z + (γ.1 1 1 : ℂ)) ^ k * f z := by
--   have := SlashInvariantForm.slash_action_eqn' k Γ f γ z
--   rw [this]
--   norm_cast


lemma SlashInvariantForm_neg_one_in_lvl_odd_wt_eq_zero
  (k : ℤ) (hkO : Odd k) (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ) [FunLike F ℍ ℂ]
  [SlashInvariantFormClass F Γ k] [AddCommMonoid F] [Module ℤ F] (hzero : ⇑(0 : F) = 0) (f : F):
    f = 0 := by
  apply DFunLike.ext
  intro z
  have hO : (-1 :ℂ)^k = -1 := by
    apply hkO.neg_one_zpow
  have := slash_action_eqn' k Γ f
  have HI := slash_action_eqn' k Γ f ⟨-1, hΓ⟩ z
  simp at HI

  --rw [HIn] at HI
  have : (((-1 : GL(2, ℤ)) : GL (Fin 2) ℤ) : Matrix _ _ ℤ) = !![-1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simpa using by rfl
  simp [this] at HI
  rw [hO] at HI
  simp at HI
  rw [hzero]
  exact CharZero.eq_neg_self_iff.mp HI


lemma SIF_Top_Odd_Wt_eq_zero (k : ℤ) (hkO : Odd k)
  (f : SlashInvariantForm ⊤ k):
  f = 0 := by
  apply SlashInvariantForm_neg_one_in_lvl_odd_wt_eq_zero k hkO
  simp
  simp

lemma toSIF_injective (k : ℤ) (Γ : Subgroup SL(2, ℤ)): Function.Injective
  (@toSlashInvariantForm Γ k) := by
  intro f g
  intro h
  rw [DFunLike.ext_iff] at *
  intro z
  have hz := h z
  simpa using hz

lemma ModularForm_to_SIF_ext (k : ℤ) (f g : ModularForm Γ k) : f = g ↔ f.1 = g.1:= by
  refine Iff.symm (Function.Injective.eq_iff ?I)
  apply toSIF_injective

lemma ModularForms_Top_Odd_Wt_eq_zero (k : ℤ) (hkO : Odd k) (f : ModularForm Γ k) (hΓ : -1 ∈ Γ) :
    f = 0 := by
  apply SlashInvariantForm_neg_one_in_lvl_odd_wt_eq_zero k hkO _ hΓ
  simp

lemma eiseinsteinSeries_Odd_wt_eq_zero (k : ℤ) ( hk : 3 ≤ k) (hkO : Odd k)
    (a : Fin 2 → ZMod (1 : ℕ+)) : eisensteinSeries_MF hk a = 0 := by
  apply ModularForms_Top_Odd_Wt_eq_zero k hkO
  simp
  apply (ZMod.subsingleton_iff.mpr rfl).elim
