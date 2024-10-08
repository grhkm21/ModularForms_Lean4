/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open Complex Real ModularForm SlashInvariantForm

open scoped BigOperators NNReal Classical Filter UpperHalfPlane

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

noncomputable section

/-! ### Eisenstein series -/

/-- The function on `ℤ × ℤ` whose sum defines an Eisenstein series.-/
def eise (k : ℤ) (z : ℍ) : ℤ × ℤ → ℂ := fun x => 1 / (x.1 * z.1 + x.2) ^ k
instance : TopologicalSpace C(ℍ, ℂ) :=
  inferInstance

def AbsEise (k : ℤ) (z : ℍ) : ℤ × ℤ → ℝ := fun x => Complex.abs (1 / (x.1 * z.1 + x.2) ^ k)

/-- The Eisenstein series of weight `k : ℤ` -/
def Eisenstein_tsum (k : ℤ) : ℍ → ℂ := fun z => ∑' x : ℤ × ℤ, eise k z x

def AbsEisenstein_tsum (k : ℤ) : ℍ → ℝ := fun z => ∑' x : ℤ × ℤ, AbsEise k z x

namespace EisensteinSeries

theorem Moebius_aux_lem (k : ℤ) (a b c d i1 i2 : ℂ) (z : ℍ) (h : c * z + d ≠ 0) :
    ((i1 * ((a * z + b) / (c * z + d)) + i2) ^ k)⁻¹ =
      (c * z + d) ^ k * (((i1 * a + i2 * c) * z + (i1 * b + i2 * d)) ^ k)⁻¹ :=
  by
  have h1 : i1 * ((a * z + b) / (c * z + d)) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  rw [h1]
  have h2 : i1 * (a * z + b) / (c * z + d) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  rw [h2]
  have h3 := div_add' (i1 * (a * z + b)) i2 (c * z + d) h
  rw [h3]
  rw [div_eq_inv_mul, mul_comm]
  ring_nf
  field_simp

-- This is the permutation of the summation index coming from the moebius action
def MoebiusPerm (A : SL(2,ℤ)) : ℤ × ℤ → ℤ × ℤ := fun z =>
  (z.1 * A.1 0 0 + z.2 * A.1 1 0, z.1 * A.1 0 1 + z.2 * A.1 1 1)

theorem det_SL_eq_one (M : SL(2,ℤ)) : M.1 0 0 * M.1 1 1 -(M.1 0 1 * M.1 1 0) = 1 := by
  have H := Matrix.det_fin_two M.1
  simp at *
  rw [← H]

lemma MoebiusPerm_left_inv (A : SL(2,ℤ)) (z : ℤ × ℤ) : MoebiusPerm A⁻¹ (MoebiusPerm A z) = z := by
    simp_rw [MoebiusPerm]
    ring_nf
    have hdet := det_SL_eq_one A
    have hi := Matrix.SpecialLinearGroup.SL2_inv_expl A
    rw [hi] at *
    simp at *
    ring_nf
    have h1: z.fst * A.1 0 0 * A.1 1 1 - z.fst * A.1 0 1 * A.1 1 0 = z.fst := by
      trans (z.fst * (A.1 0 0 * A.1 1 1 -  A.1 0 1 * A.1 1 0))
      ring
      rw [hdet]
      apply mul_one
    have h2 :  A.1 0 0 * A.1 1 1* z.snd -  A.1 0 1 * A.1 1 0 * z.snd = z.snd := by
      trans ((A.1 0 0 * A.1 1 1 -  A.1 0 1 * A.1 1 0)* z.snd )
      ring
      rw [hdet]
      apply one_mul
    rw [h1,h2]

lemma MoebiusPerm_right_inv (A : SL(2,ℤ)) (z : ℤ × ℤ) : MoebiusPerm A (MoebiusPerm A⁻¹ z) = z := by
    have := MoebiusPerm_left_inv A⁻¹
    rw [inv_inv] at this
    apply this

def MoebiusEquiv (A : SL(2,ℤ)) : ℤ × ℤ ≃ ℤ × ℤ
    where
  toFun := MoebiusPerm A
  invFun := MoebiusPerm A⁻¹
  left_inv z := by apply MoebiusPerm_left_inv A
  right_inv z := by apply MoebiusPerm_right_inv A

-- How the Eise function changes under the Moebius action
theorem eise_Moebius (k : ℤ) (z : ℍ) (A : SL(2,ℤ)) (i : ℤ × ℤ) :
    eise k (A • z) i =
      (A.1 1 0 * z.1 + A.1 1 1) ^ k * eise k z (MoebiusEquiv A i) := by
  convert eisSummand_SL2_apply k ![i.fst, i.snd] _ _
  · simp [eise, eisSummand]
  · simp [eise, eisSummand, MoebiusEquiv, MoebiusPerm, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]

#check eisensteinSeries_SIF
-- /--The Slash Invariant Form defined by an Eisenstein series-/
-- def Eisenstein_SIF (Γ : Subgroup SL(2,ℤ)) (k : ℤ) : SlashInvariantForm Γ k where
--   toFun := Eisenstein_tsum k
--   slash_action_eq' := by
--     intro A
--     ext1 x
--     simp_rw [slash_action_eq'_iff]
--     rw [Eisenstein_tsum]
--     simp only [UpperHalfPlane.subgroup_to_sl_moeb, UpperHalfPlane.sl_moeb]
--     convert (tsum_congr (eise_Moebius k x A))
--     have h3 := Equiv.tsum_eq (MoebiusEquiv A) (eise k x)
--     rw [tsum_mul_left, h3, Eisenstein_tsum]
--     norm_cast
