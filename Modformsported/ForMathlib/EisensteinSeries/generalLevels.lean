/- 
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.ModularForm
import Modformsported.ForMathlib.AuxpLemmas
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups 


noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R  

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

def lvl_N_congr (N : ℕ) (a b : ℤ ) := {x : ℤ × ℤ  | (x.1 : ZMod N) = a ∧ (x.2 : ZMod N) = b ∧ (x.1).gcd (x.2) = 1 }

def lvl_N_congr' (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ  | (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ 
  (f 0).gcd (f 1) = 1 }

@[simp]
lemma lvl_N_congr_mem (N : ℕ) (a b : ℤ ) (x : ℤ × ℤ) : x ∈ lvl_N_congr N a b ↔ 
  (x.1 : ZMod N) = a ∧ (x.2 : ZMod N) = b ∧ (x.1).gcd (x.2) = 1 := by rfl

@[simp]
lemma lvl_N_congr'_mem (N : ℕ) (a b : ℤ ) (f : (Fin 2) → ℤ ) : f ∈ lvl_N_congr' N a b ↔ 
  (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ (f 0).gcd (f 1) = 1 := by rfl 

section

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

def SpecialLinearGroup.transpose ( A:  Matrix.SpecialLinearGroup n R)  :  
  Matrix.SpecialLinearGroup n R  := by
  use A.1.transpose
  rw [Matrix.det_transpose]
  apply A.2

section gcd_to_sl_lemmas

def gcd_one_to_SL (a b : ℤ) (hab : a.gcd b =1) : SL(2, ℤ) := by
  use !![a, -Int.gcdB a b;  b, Int.gcdA a b]
  simp
  have := Int.gcd_eq_gcd_ab a b 
  rw [hab] at this
  simp at this
  rw [this]
  ring

def gcd_one_to_SL_bot_row (a b : ℤ) (hab : a.gcd b =1) : SL(2, ℤ) := by
  use !![ Int.gcdB a b,  -Int.gcdA a b; a, b]
  simp
  have := Int.gcd_eq_gcd_ab a b 
  rw [hab] at this
  simp at this
  rw [this]
  ring

def SL_to_gcd_one_fst_col (A: SL(2,ℤ)) : (A.1 0 0).gcd (A.1 0 1) = 1 := by
    rw [Int.gcd_eq_one_iff_coprime]
    rw [IsCoprime]
    use (A.1 1 1)
    use -(A.1 1 0)
    have T:= EisensteinSeries.det_SL_eq_one A
    norm_cast at *
    ring_nf
    rw [mul_comm] 
    norm_cast at *
    have : A.1 0 1 * A.1 1 0 = A.1 1 0 * A.1 0 1 := by ring
    rw [this] at T
    exact T

   
lemma SL2_gcd (a b : ℤ) (hab : a.gcd b = 1) (A : SL(2,ℤ)) : 
  (Matrix.vecMul (![a,b]) A.1 0).gcd (Matrix.vecMul (![a,b]) A.1 1) = 1  := by
    let C := SpecialLinearGroup.transpose ((gcd_one_to_SL a b hab)) *A
    have := SL_to_gcd_one_fst_col C
    simp at this
    rw [SpecialLinearGroup.transpose, gcd_one_to_SL] at this
    simp at this
    simp_rw [Matrix.vecMul] at *
    simp at *
    norm_cast at *
    simp_rw [Matrix.vecHead, Matrix.vecTail,  Matrix.mul, Matrix.dotProduct, Matrix.transpose] at *
    simp at *
    simp_rw [Matrix.vecHead] at this
    simp at this
    exact this

def GammaSLinv (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) (f : lvl_N_congr' N a b) : 
  (lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) := by
  use Matrix.vecMul f.1 A.1 
  simp
  have hf := f.2  
  rw [lvl_N_congr'_mem] at hf
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A
  simp_rw [Matrix.vecMul, Matrix.vecHead] at *
  simp at *
  simp_rw [Matrix.vecHead,Matrix.vecTail, hf.1, hf.2.1]
  simp
  convert this

@[simp]
lemma GammaSLinv_apply (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) (f : lvl_N_congr' N a b) : 
  (GammaSLinv N a b A f).1 = Matrix.vecMul f.1 A.1 := by rfl

lemma a_a_inv  (a b : ℤ )  (A  : SL(2,ℤ)) : 
  Matrix.vecMul (Matrix.vecMul (![a,b]) A.1) A⁻¹.1 = ![a,b] := by
  --have hi := Matrix.vecMul_vecMul ![a,b] 
  simp
  rw [Matrix.mul_adjugate, A.2]
  simp

def GammaSLinv' (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) 
  (f : lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) : 
  (lvl_N_congr' N a b) := by
  use Matrix.vecMul f.1 A⁻¹.1 
  have hf := f.2  
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A⁻¹
  have hi := Matrix.vecMul_vecMul ![(a : ZMod N),(b : ZMod N)] 
    (Matrix.map A.1 ((↑) : ℤ→  (ZMod N))) (Matrix.map A⁻¹.1 ((↑) : ℤ→  (ZMod N)))
  have hi2 := a_a_inv a b A  
  have hh :  (![(a : ZMod N),(b : ZMod N)] : (Fin 2) → (ZMod N)) =  ((↑) : ℤ →  (ZMod N)) ∘ ![a,b] :=
    by 
    funext i
    fin_cases i
    simp
    rfl
  have HI : ((↑) : ℤ →  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))  = 
    (![(a : ZMod N),(b : ZMod N)] : (Fin 2) → (ZMod N)) := by
    rw [hh]
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl] at *
    convert hi
    ext i
    fin_cases i
    simp only [Fin.mk_zero, comp_apply, Matrix.vecMul_vecMul]
    simp_rw [Matrix.vecMul, Matrix.vecHead,  Matrix.dotProduct] at *
    simp_rw [Matrix.vecHead,Matrix.vecTail,Matrix.transpose,Matrix.cramer,Matrix.cramerMap, Matrix.mul]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.sum_univ_two,
      Matrix.cons_val_one, Matrix.head_fin_const, mul_neg, Int.cast_add, Int.cast_mul, Int.cast_neg, Matrix.map_apply,
      Matrix.vec2_dotProduct, Matrix.head_cons]
    rw [hf.1, hf.2.1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add,
      Int.cast_mul]
    ring
    simp only [Fin.mk_one, comp_apply, Matrix.vecMul_vecMul]
    simp_rw [Matrix.vecMul, Matrix.vecHead,  Matrix.dotProduct,Matrix.mul] at *
    simp only [Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.sum_univ_two, Matrix.cons_val_zero, mul_neg, Matrix.head_fin_const, Int.cast_add, Int.cast_neg, Int.cast_mul,
      Matrix.map_apply, Matrix.vec2_dotProduct]
    rw [hf.1, hf.2.1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add,
      Int.cast_mul]
    ring
    rw [←hi2]
    simp only [Matrix.vecMul_vecMul]
    ext i
    fin_cases i
    simp only [Fin.mk_zero, comp_apply]
    simp_rw [Matrix.vecMul, Matrix.vecHead,  Matrix.dotProduct,Matrix.mul] at *
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.dotProduct_cons, Fin.sum_univ_two, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add, Int.cast_mul,
      Matrix.map_apply, Matrix.vec2_dotProduct, Matrix.head_fin_const, Int.cast_neg, mul_neg]
    simp_rw [Matrix.vecMul, Matrix.vecHead,  Matrix.dotProduct,Matrix.mul] at *
    simp only [Finset.univ_unique, Fin.default_eq_zero, mul_neg, Finset.sum_neg_distrib, Finset.sum_singleton,
      Int.cast_neg, Int.cast_mul]
    simp_rw [Matrix.vecTail]
    simp only [comp_apply, Fin.succ_zero_eq_one]
    simp_rw [Matrix.vecMul, Matrix.vecHead,  Matrix.dotProduct,Matrix.mul] at *
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.dotProduct_cons, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.mk_one, comp_apply, mul_neg, Int.cast_add,
      Int.cast_mul, Int.cast_neg, Matrix.map_apply, Matrix.vec2_dotProduct, Matrix.head_fin_const]
    simp_rw [Matrix.vecTail, Matrix.vecHead, Matrix.dotProduct,Matrix.mul]
    simp only [Finset.univ_unique, Fin.default_eq_zero, comp_apply, Finset.sum_singleton, Fin.succ_zero_eq_one,
      Int.cast_mul]
  constructor
  have HI0 : (((↑) : ℤ→  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))) 0 = (a : ZMod N) := by 
    rw [HI]
    simp only [Matrix.cons_val_zero]
  simpa using HI0  
  constructor
  have HI1 : (((↑) : ℤ→  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))) 1 = (b : ZMod N) := by 
    rw [HI]
    simp [Matrix.cons_val_zero]
  simpa using HI1
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A⁻¹
  convert this
  ext i
  fin_cases i
  rfl
  rfl
  ext i
  fin_cases i
  rfl
  rfl

lemma GammaSLleftinv (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ))  (v : lvl_N_congr' N a b) : 
    GammaSLinv' N a b A  (GammaSLinv N a b A v) = v := by
  rw [GammaSLinv', GammaSLinv]
  simp 
  apply Subtype.ext
  simp  
  rw [Matrix.mul_adjugate, A.2]
  simp

lemma GammaSLrightinv (N : ℕ)  (a b : ℤ ) (A  : SL(2,ℤ)) 
  (v : lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) : 
    GammaSLinv N a b A  (GammaSLinv' N a b A v) = v := by
  rw [GammaSLinv', GammaSLinv]
  simp 
  apply Subtype.ext
  simp    
  rw [Matrix.adjugate_mul, A.2]
  simp

def GammaSLinv_equiv (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) : (lvl_N_congr' N a b) ≃ 
  (lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) where
    toFun := GammaSLinv N a b A
    invFun := GammaSLinv' N a b A 
    left_inv v:= GammaSLleftinv N a b A v
    right_inv v:= GammaSLrightinv N a b A v

def Gammainv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (f : lvl_N_congr' N a b) : (lvl_N_congr' N a b) := by 
  use Matrix.vecMul f.1 γ.1.1 
  simp
  simp_rw [Matrix.vecMul]
  simp
  have hγ := (Gamma_mem N _).1 γ.2
  have hf := f.2
  rw [hγ.1, hγ.2.2.1, hγ.2.2.2, hγ.2.1, hf.1, hf.2.1]
  simp
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 γ
  simp_rw [Matrix.vecMul,  Matrix.dotProduct, Matrix.vecMul] at this
  convert this
  simp
  simp

/-
variables (N : ℕ)  (a b : ℤ ) (A  : SL(2,ℤ))(v : lvl_N_congr' N a b) 
#check  GammaSLinv N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1) A⁻¹ (GammaSLinv N a b A v) 


lemma GammaSLleftinv (N : ℕ)  (a b : ℤ ) (A  : SL(2,ℤ))(v : lvl_N_congr' N a b) : 
  GammaSLinv N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1) A⁻¹  (GammaSLinv N a b A v)  := by
-/


lemma Gammaleftinv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (v : lvl_N_congr' N a b) : 
  Gammainv N a b γ⁻¹ (Gammainv N a b γ v) = v := by
  simp_rw [Gammainv]
  simp only [SubgroupClass.coe_inv,  Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp 
  rw [Matrix.mul_adjugate]
  rw [γ.1.2]
  simp

lemma Gammarightinv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (v : lvl_N_congr' N a b) : 
  Gammainv N a b γ (Gammainv N a b γ⁻¹ v) = v := by
  simp_rw [Gammainv]
  simp only [SubgroupClass.coe_inv,  Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp 
  rw [Matrix.adjugate_mul]
  rw [γ.1.2]
  simp
  

def Gammainv_Equiv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) : (lvl_N_congr' N a b) ≃ (lvl_N_congr' N a b) 
    where
  toFun := Gammainv N a b γ 
  invFun := Gammainv N a b γ⁻¹ 
  left_inv v:= by 
    apply Gammaleftinv
  right_inv v:= by
    apply Gammarightinv


def Gammainv_Equiv_eq (N : ℕ)  (a b : ℤ ) (γ  : Gamma N) (v : (lvl_N_congr' N a b)) : 
  ((Gammainv N a b γ) v).1 = 
    ( (Matrix.SpecialLinearGroup.toLin' (SpecialLinearGroup.transpose γ.1) ).toEquiv) v.1 := by
  simp_rw [Gammainv]
  simp
  simp_rw [Matrix.SpecialLinearGroup.toLin'_apply, SpecialLinearGroup.transpose]
  simp
  rw [Matrix.mulVec_transpose]


def prod_fun_equiv : ℤ × ℤ ≃ (Fin 2 → ℤ) := by exact (piFinTwoEquiv fun _ => ℤ).symm

def index_equiv (N : ℕ)  (a b : ℤ ) : (lvl_N_congr' N a b) ≃ (lvl_N_congr N a b)  := by
  apply Equiv.subtypeEquiv (piFinTwoEquiv fun _ => ℤ)
  rw [piFinTwoEquiv ]
  simp


lemma summable_Eisenstein_N_tsum (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ): 
  Summable (fun (x : (lvl_N_congr  N a b)) => (eise k z  x.1) ) := by 
  apply (Eisenstein_tsum_summable k z hk).subtype



def feise (k : ℤ) (z : ℍ) (v : (lvl_N_congr'  N a b)) : ℂ := (eise k z ((piFinTwoEquiv fun _ => ℤ) v.1))
  
/-- The Eisenstein series of weight `k : ℤ` -/
def Eisenstein_N_tsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (lvl_N_congr'  N a b), 
  (feise k z  x)


lemma summable_Eisenstein_N_tsum' (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ): 
  Summable (fun (x : (lvl_N_congr'  N a b)) => feise k z x)  := by 
  have : (fun (x : (lvl_N_congr'  N a b)) => feise k z x) = 
   (fun (x : (lvl_N_congr  N a b)) => (eise k z  x.1)) ∘ (index_equiv N a b) := by 
    ext1 v
    simp
    congr
  rw [this, Equiv.summable_iff] 
  apply summable_Eisenstein_N_tsum k hk



lemma feise_eq_one_div_denom (k : ℤ) (z : ℍ) (v : (lvl_N_congr'  N a b))  : feise k z v = 
  1/(UpperHalfPlane.denom (gcd_one_to_SL_bot_row (v.1 0) (v.1 1) v.2.2.2) z)^(k) := by 
  rw [feise, denom,gcd_one_to_SL_bot_row]
  simp
  rw [eise]
  simp



def equivla (A : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ :=  
  (prod_fun_equiv.trans (Matrix.SpecialLinearGroup.toLin' A).toEquiv).trans  prod_fun_equiv.symm



lemma averaver (A: SL(2, ℤ)) : equivla  (SpecialLinearGroup.transpose A)  = MoebiusEquiv A  := by
  rw [equivla, prod_fun_equiv]
  simp only [Equiv.symm_symm, Equiv.coe_trans, piFinTwoEquiv_apply, LinearEquiv.coe_toEquiv, 
  piFinTwoEquiv_symm_apply,
    MoebiusEquiv,MoebiusPerm]
  simp
  ext1 v
  simp
  constructor
  rw [Matrix.SpecialLinearGroup.toLin'_apply,SpecialLinearGroup.transpose ]
  simp
  rw [Matrix.mulVec, Matrix.dotProduct]
  simp
  ring_nf
  have  : v.snd * A.1 1 0 = A.1 1 0 * v.snd := by ring
  congr
  rw [Matrix.SpecialLinearGroup.toLin'_apply,SpecialLinearGroup.transpose ]
  simp
  rw [Matrix.mulVec, Matrix.dotProduct]
  simp 
  ring_nf
  congr

theorem feise_Moebius (k : ℤ) (z : ℍ) (N : ℕ) (A : Gamma N) (i : (lvl_N_congr'  N a b)) :
    feise k (A • z) i =
      (A.1 1 0 * z.1 + A.1 1 1) ^ k * feise k z ((Gammainv_Equiv N a b A)  i) := by
    simp_rw [feise,UpperHalfPlane.specialLinearGroup_apply]
    have := eise_Moebius k z A.1 ((piFinTwoEquiv fun _ => ℤ) i.1)
    convert this
    rw [←averaver A, equivla,Gammainv_Equiv]
    simp
    rw [Gammainv_Equiv_eq]
    simp
    simp_rw [Matrix.SpecialLinearGroup.toLin'_apply,prod_fun_equiv]
    simp
    constructor
    rfl
    rfl

def Eisenstein_SIF_lvl_N (N : ℕ) (k a b : ℤ) : SlashInvariantForm (Gamma N) k
    where
  toFun := Eisenstein_N_tsum k N a b 
  slash_action_eq' := by
    intro A
    ext1 x
    simp_rw [slash_action_eq'_iff]
    rw [Eisenstein_N_tsum]
    simp only [UpperHalfPlane.subgroup_to_sl_moeb, UpperHalfPlane.sl_moeb]
    convert (tsum_congr (feise_Moebius k x N A))
    have h3 := Equiv.tsum_eq (Gammainv_Equiv N a b A) (feise k x)
    rw [tsum_mul_left, h3, Eisenstein_N_tsum]
    norm_cast

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f


lemma int_cast_abs_self (N : ℤ) : (N : ZMod (Int.natAbs N)) = 0 := by
  refine Iff.mpr (ZMod.int_cast_zmod_eq_zero_iff_dvd N (Int.natAbs N)) ?_
  simp only [Int.coe_natAbs, abs_dvd, dvd_refl]

lemma T_pow_N_mem_Gamma (N : ℤ) : (ModularGroup.T^N) ∈ _root_.Gamma (Int.natAbs N) := by
  simp
  simp_rw [ModularGroup.coe_T_zpow]
  simp
  apply int_cast_abs_self
  
lemma T_pow_N_mem_Gamma' (N n : ℤ) : (ModularGroup.T^N)^n ∈ _root_.Gamma (Int.natAbs N) := by
  exact Subgroup.zpow_mem (_root_.Gamma (Int.natAbs N)) (T_pow_N_mem_Gamma N) n


local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)


lemma slash_apply (k : ℤ) (A : SL(2,ℤ)) (f : ℍ → ℂ) (z : ℍ): (f∣[k,A]) z = 
  f (A • z)  * denom A z ^ (-k) := by
  simp only [SL_slash, slash_def, ModularForm.slash,denom, Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, 
    zpow_neg, Matrix.SpecialLinearGroup.det_coe, ofReal_one, one_zpow, mul_one, subgroup_to_sl_moeb]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply,
    ofReal_int_cast, uhc, UpperHalfPlane.sl_moeb]
  norm_cast
  rw [zpow_neg]
  congr

lemma denom_cocycle_SL  (N : ℕ) (a b : ℤ) (A : SL(2,ℤ)) (v : (lvl_N_congr'  N a b)) (z : ℍ) :
  denom ((gcd_one_to_SL_bot_row (v.1 0) (v.1 1) v.2.2.2) * A) z = 
    denom ((gcd_one_to_SL_bot_row ((GammaSLinv_equiv N a b A v).1 0) 
      ((GammaSLinv_equiv N a b A v).1 1) (GammaSLinv_equiv N a b A v).2.2.2)) z := by
  simp_rw [denom, gcd_one_to_SL_bot_row, GammaSLinv_equiv, GammaSLinv]
  simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul,
    Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.mul_eq_mul, uhc, Equiv.coe_fn_mk, GammaSLinv_apply,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_fin_const, ofReal_int_cast, Matrix.head_cons]
  simp_rw [Matrix.vecMul, Matrix.mul, Matrix.dotProduct]  
  simp

lemma Eisenstein_lvl_N_Sl_inv (N k: ℕ) (hk : 3 ≤ k) (a b : ℤ) (A : SL(2,ℤ)) : 
  (((Eisenstein_SIF_lvl_N N (k : ℤ) a b).1)∣[(k : ℤ),A]) = 
    (((Eisenstein_SIF_lvl_N N k (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)).1)) := by
 
  ext1 z
  have := slash_apply k A ((Eisenstein_SIF_lvl_N N k a b).1) z
  rw [this] 
  simp only [SlashInvariantForm.toFun_eq_coe]
  simp_rw [Eisenstein_SIF_lvl_N, Eisenstein_N_tsum]
  simp only [SlashInvariantForm.coe_mk]
  rw [Eisenstein_N_tsum]
  rw [Eisenstein_N_tsum]
  have := @feise_eq_one_div_denom N a b k (A • z) 
  have t2 := @feise_eq_one_div_denom N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1) k (z)


  simp only [piFinTwoEquiv_apply, Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply,
    ofReal_int_cast, uhc]
  convert (Equiv.tsum_eq (GammaSLinv_equiv N a b A) _)
  norm_cast
  rw [←Summable.tsum_mul_right]
  apply tsum_congr
  intro v
  simp_rw [this]
  rw [t2]
  simp only [cpow_int_cast, one_div, zpow_neg]
  rw [←mul_inv]
  congr
  rw [←mul_zpow]
  congr
  have cocy:= UpperHalfPlane.denom_cocycle (gcd_one_to_SL_bot_row (v.1 0) (v.1 1) v.2.2.2) A z
  have seq : A • z = smulAux A z := by rfl
  rw [seq]
  rw [←cocy]
  have HF:= denom_cocycle_SL N a b A v z
  exact HF
  apply summable_Eisenstein_N_tsum' k hk 
  exact T25Space.t2Space
  
lemma tsum_subtype_le {α : Type} (f : α → ℝ) (β : Set α) (hf : ∀ a : α, 0 ≤ f a) (hf2 : Summable f) :
  (∑' (b : β), f b) ≤ (∑' (a : α), f a) := by
  have := tsum_subtype_add_tsum_subtype_compl hf2 β
  rw [← this]
  simp
  apply tsum_nonneg
  intro b
  apply hf b

lemma UBOUND (N : ℕ) (a b : ℤ) (k : ℕ) (hk : 3 ≤ k) (z : ℍ): 
  Complex.abs ((((Eisenstein_SIF_lvl_N N k a b))) z) ≤ (AbsEisenstein_tsum k z) := by
  simp_rw [Eisenstein_SIF_lvl_N, AbsEisenstein_tsum, Eisenstein_N_tsum]
  simp
  apply le_trans (abs_tsum' ?_)
  simp_rw [feise, eise]
  have := Equiv.tsum_eq prod_fun_equiv.symm (fun x : ℤ × ℤ => (AbsEise k z x))
  rw [←this]
 
  have Ht := tsum_subtype_le (fun x : (Fin 2 → ℤ)  => (AbsEise k z (prod_fun_equiv.symm x))) 
    (lvl_N_congr' N a b) ?_ ?_
  simp_rw [AbsEise] at *
  simp at *
  apply le_trans Ht
  rfl
  intro v
  simp_rw [AbsEise]
  simp
  have := real_eise_is_summable k z hk
  rw [←Equiv.summable_iff prod_fun_equiv.symm] at this
  exact this
  rw [←summable_iff_abs_summable]
  apply summable_Eisenstein_N_tsum' k hk


theorem lvl_N_periodic (N : ℕ) (k : ℤ) (f : SlashInvariantForm (Gamma N) k) :
    ∀ (z : ℍ) (n : ℤ), f (((ModularGroup.T^N)^n)  • z) = f z :=
  by
  have h := SlashInvariantForm.slash_action_eqn' k (Gamma N) f
  simp only [SlashInvariantForm.slash_action_eqn']
  intro z n
  simp only [Subgroup.top_toSubmonoid, subgroup_to_sl_moeb, Subgroup.coe_top, Subtype.forall,
    Subgroup.mem_top, forall_true_left] at h 
  have Hn :=  (T_pow_N_mem_Gamma' N n)
  simp only [zpow_coe_nat, Int.natAbs_ofNat] at Hn   
  have H:= h ((ModularGroup.T^N)^n) Hn z
  rw [H]
  have h0 : (((ModularGroup.T^N)^n) : GL (Fin 2) ℤ) 1 0 = 0  := by 
    rw [slcoe]
    have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by 
      rw [zpow_mul]
      simp
    rw [this]
    rw [ModularGroup.coe_T_zpow (N*n)]
    rfl
  have h1: (((ModularGroup.T^N)^n) : GL (Fin 2) ℤ) 1 1 = 1  := by 
    rw [slcoe]
    have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by 
      rw [zpow_mul]
      simp
    rw [this]
    rw [ModularGroup.coe_T_zpow (N*n)]
    rfl   
  rw [h0,h1]
  ring_nf
  simp

theorem Eisenstein_series_is_bounded (a b: ℤ) (N k: ℕ) (hk : 3 ≤ k) (A : SL(2, ℤ)) (hN : 0 < (N : ℤ)) :
    IsBoundedAtImInfty ( (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1∣[(k : ℤ),A]) :=
  by
  simp_rw [UpperHalfPlane.bounded_mem] at *
  let M : ℝ := 8 / rfunct (lbpoint N 2 <| by linarith) ^ k * Complex.abs (riemannZeta (k - 1))
  use M
  use 2
  intro z hz
  obtain ⟨n, hn⟩ := (upp_half_translation_N z N hN)
  rw [Eisenstein_lvl_N_Sl_inv]
  have := lvl_N_periodic N k (Eisenstein_SIF_lvl_N N k (Matrix.vecMul ![a, b] (A.1) 0) 
    (Matrix.vecMul ![a, b] (A.1) 1)) z n
  simp only [SlashInvariantForm.toFun_eq_coe, Real.rpow_int_cast, ge_iff_le]
  rw [←this]  
  apply le_trans (UBOUND N _ _ k hk ((ModularGroup.T ^ N) ^ n • z))
  let Z := ((ModularGroup.T ^ N) ^ n) • z
  have hZ : Z ∈ upperHalfSpaceSlice N 2 :=
    by
    norm_cast at *
    rw [slice_mem] at *
    constructor
    apply hn.1
    simp only [map_zpow, map_pow, abs_ofReal, ge_iff_le] at *
    have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by 
      rw [zpow_mul]
      simp
    rw [this] at *
    rw [modular_T_zpow_smul] at *
    simp
    have va := UpperHalfPlane.vadd_im ((N : ℝ)*n) z
    simp_rw [UpperHalfPlane.im] at *
    simp at va
    rw [va]
    convert hz
    simp
    apply z.2.le 
  have hkk : 3 ≤ Int.natAbs k := by norm_cast  
  have := AbsEisenstein_bound_unifomly_on_stip (Int.natAbs k) hkk N 2 (by linarith) ⟨Z, hZ⟩
  convert this
  apply hk
  
lemma  Eisenstein_lvl_N_tendstolocunif2 (a b: ℤ) (N k : ℕ) (hk : 3 ≤ k) :
  TendstoUniformly ((fun (s : Finset (lvl_N_congr'  N a b)) => 
    (fun (z : ℍ) => ∑ x in s, eise k z ((piFinTwoEquiv fun _ => ℤ).1 x)  ) ) )
    ( fun (z : ℍ) => (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1 z) atTop  := by  
  --rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  --intro K hK hK2
  rw [Eisenstein_SIF_lvl_N]
  
  simp [Eisenstein_N_tsum, feise]

  apply tendstoUniformly_tsum

lemma  Eisenstein_lvl_N_tendstolocunif (a b: ℤ) (N k : ℕ) (hk : 3 ≤ k) :
  TendstoLocallyUniformlyOn ((fun (x : (lvl_N_congr  N a b)) => extendByZero 
    (fun (z : ℍ) => eise k z  x.1) ) )
    (extendByZero (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1) ⊤ ℍ' := by  
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  intro K hK hK2
  sorry
  sorry
  rw [Eisenstein_SIF_lvl_N]
  simp
  


local notation "↑ₕ" => holExtn

theorem Eisenstein_lvl_N_is_holomorphic (a b: ℤ) (N k : ℕ) (hk : 3 ≤ k) :
    IsHolomorphicOn (↑ₕ (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1) :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  sorry
/-
open Set Metric MeasureTheory Filter Complex intervalIntegral

open scoped Real Topology

variable {α β 𝕜 E F : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem tendstoUniformlyOn_tsum' {f : α → β → F} (hu : Summable u) {s : Set β} (I : Set α)
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t : Finset I => fun x => ∑ n in t, f n x) (fun x => ∑' n : I, f n x) atTop
      s := by
  have :=  tendstoUniformlyOn_tsum hu hfu  
  rw [tendstoUniformlyOn_iff ] at *
  simp at *
-/  


  