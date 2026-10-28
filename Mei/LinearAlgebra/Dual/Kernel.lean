/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mei.Algebra.Module.Primitive

/-!
# Kernels of linear functionals

If a common kernel has codimension two, two members of the defining family
already cut it out. The family may be infinite and may contain zero or
redundant functionals. The proof uses Mathlib's dimension formula for the kernel
of a nonzero functional and strict monotonicity of finite dimension.

Contracting two equations against a vector outside their common kernel gives
one equation for the sum of that kernel and the line through the vector.

In a finite free integer module of rank at most two, any primitive vector in the
kernel of a nonzero functional spans that kernel, identifying its primitive normal direction.
-/

public section

namespace LinearMap

open Module

/-- In a finite free `ℤ`-module of rank at most two, the kernel of a nonzero functional is
spanned by any of its primitive vectors. -/
theorem ker_eq_span_singleton_of_isPrimitive {V : Type*} [AddCommGroup V] [Module.Free ℤ V]
    [Module.Finite ℤ V] (hV : finrank ℤ V ≤ 2) {e : V →ₗ[ℤ] ℤ} (he : e ≠ 0) {v : V}
    (hv : TauCeti.IsPrimitive v) (hev : e v = 0) : ker e = ℤ ∙ v := by
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hv
  obtain ⟨w, hw⟩ : ∃ w, e w ≠ 0 := by
    by_contra! h
    exact he (LinearMap.ext h)
  refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr hev)
  rw [mem_ker] at hx
  rw [Submodule.mem_span_singleton]
  -- three vectors in a module of rank at most two are dependent
  have hdep : ¬LinearIndependent ℤ ![v, x, w] := fun h => by
    have := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  have hc2 : c 2 = 0 := by
    have h := congr(e $hc)
    simp only [map_add, map_zsmul, hev, hx, map_zero, smul_eq_mul, mul_zero, zero_add,
      mul_eq_zero] at h
    exact h.resolve_right hw
  have hc0 : c 0 + c 1 * f x = 0 := by
    simpa [hf, hc2] using congr(f $hc)
  have hc1 : c 1 ≠ 0 := by
    intro h
    fin_cases i <;> simp_all
  refine ⟨f x, smul_right_injective V hc1 ?_⟩
  have h : c 0 • v + c 1 • x = 0 := by simpa [hc2] using hc
  simp only [smul_smul]
  have hcancel : c 1 * f x = -c 0 := by linarith
  rw [hcancel, neg_smul, neg_eq_iff_add_eq_zero, h]

section Contraction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Contracting two functionals against a vector outside their common kernel
cuts out the sum of that common kernel and the vector's span. -/
theorem ker_apply_smul_sub_apply_smul (f g : V →ₗ[K] K) {v : V}
    (hv : v ∉ f.ker ⊓ g.ker) :
    (f v • g - g v • f).ker = (f.ker ⊓ g.ker) ⊔ K ∙ v := by
  have step (f g : V →ₗ[K] K) (hf : f v ≠ 0) :
      (f v • g - g v • f).ker ≤ (f.ker ⊓ g.ker) ⊔ K ∙ v := by
    intro x hx
    have he : f v * g x = g v * f x := by
      simpa only [mem_ker, sub_apply, smul_apply, smul_eq_mul, sub_eq_zero] using hx
    have hw : x - (f x / f v) • v ∈ f.ker ⊓ g.ker := by
      constructor
      · simp [mem_ker, hf]
      · apply mem_ker.mpr
        rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero, div_mul_eq_mul_div]
        exact (eq_div_iff hf).mpr (by simpa only [mul_comm] using he)
    have hl : (f x / f v) • v ∈ K ∙ v := Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self v)
    exact Submodule.mem_sup.mpr ⟨_, hw, _, hl, sub_add_cancel _ _⟩
  apply le_antisymm
  · by_cases hf : f v = 0
    · have hg : g v ≠ 0 := fun hg => hv ⟨hf, hg⟩
      intro x hx
      have hx' : x ∈ (g v • f - f v • g).ker := by
        have he := mem_ker.mp hx
        apply mem_ker.mpr
        simpa only [sub_apply, smul_apply, smul_eq_mul, sub_eq_zero] using
          (sub_eq_zero.mp he).symm
      simpa only [inf_comm] using step g f hg hx'
    · exact step f g hf
  · refine sup_le (fun x hx => ?_) (Submodule.span_le.mpr ?_)
    · apply mem_ker.mpr
      simp [mem_ker.mp hx.1, mem_ker.mp hx.2]
    · rintro x (rfl : x = v)
      simp [mem_ker, mul_comm]

end Contraction

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A common kernel of codimension two is the intersection of two kernels
from the same family. No finiteness assumption on the family is needed. -/
theorem exists_iInf_ker_eq_inf (f : ι → V →ₗ[K] K)
    (hdim : Module.finrank K (⨅ j, (f j).ker : Submodule K V) + 2 = Module.finrank K V) :
    ∃ j k, (⨅ l, (f l).ker) = (f j).ker ⊓ (f k).ker := by
  classical
  let W : Submodule K V := ⨅ j, (f j).ker
  have hW : W ≠ ⊤ := by
    intro heq
    have hd : Module.finrank K W + 2 = Module.finrank K V := hdim
    rw [heq, finrank_top] at hd
    omega
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra! hall
    exact hW (by simp [W, hall])
  have hdimj := Module.Dual.finrank_ker_add_one_of_ne_zero hj
  have hlt : W < (f j).ker := by
    refine lt_of_le_of_ne (iInf_le _ j) ?_
    intro heq
    have := congrArg (fun U : Submodule K V => Module.finrank K U) heq
    dsimp only [W] at this
    omega
  obtain ⟨v, hvj, hvW⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨k, hk⟩ : ∃ k, v ∉ (f k).ker := by
    simpa only [W, Submodule.mem_iInf, not_forall] using hvW
  have hinf : (f j).ker ⊓ (f k).ker < (f j).ker := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    exact hk ((heq.symm ▸ hvj : v ∈ (f j).ker ⊓ (f k).ker).2)
  refine ⟨j, k, Submodule.eq_of_le_of_finrank_eq
    (le_inf (iInf_le _ j) (iInf_le _ k)) ?_⟩
  have hupper := Submodule.finrank_lt_finrank_of_lt hinf
  have hlower := Submodule.finrank_mono
    (le_inf (iInf_le (fun l => (f l).ker) j) (iInf_le (fun l => (f l).ker) k))
  omega

end LinearMap
