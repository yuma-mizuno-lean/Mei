/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.Alternating.Contraction

/-!
# Extending conormal forms by a linear functional

The exterior product of a functional with a form conormal to `W` is conormal
to the intersection of `W` with the functional's kernel. Contraction by a
vector in `W` recovers the original form, multiplied by the functional's value.
These formulas extend a conormal orientation to the boundary of a polyhedron.
`Module.Ray.wedgeCovector` packages the extension as an orientation, with
conormality, contraction and orientation-reversal laws.

The exterior product is Mathlib's `AlternatingMap.alternatizeUncurryFin`
applied to `LinearMap.smulRight`; no separate wedge-product implementation is needed.
-/

public section

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}
  {W : Submodule R M} {β : M [⋀^Fin k]→ₗ[R] R}

/-- Adjoining a functional to a conormal form gives a form conormal to the
intersection with its kernel. -/
theorem conormalForms_alternatizeUncurryFin_smulRight
    (hβ : β ∈ W.conormalForms (Fin k)) (l : M →ₗ[R] R) :
    AlternatingMap.alternatizeUncurryFin (l.smulRight β) ∈
      (W ⊓ l.ker).conormalForms (Fin (k + 1)) := by
  classical
  rw [mem_conormalForms] at hβ ⊢
  intro v j hj
  rw [AlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases haj : a = j
  · subst a
    simp [LinearMap.mem_ker.mp hj.2]
  · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm haj)
    have hz : β (a.removeNth v) = 0 :=
      hβ _ b (by simpa only [Fin.removeNth, hb, SetLike.mem_coe] using hj.1)
    simp [hz]

/-- Contracting the extended form by a vector tangent to the original form's
conormal subspace leaves only the term where the functional eats that vector. -/
theorem curryLeft_alternatizeUncurryFin_smulRight_of_mem
    (hβ : β ∈ W.conormalForms (Fin k)) (l : M →ₗ[R] R) {n : M} (hn : n ∈ W) :
    (AlternatingMap.alternatizeUncurryFin (l.smulRight β)).curryLeft n = l n • β := by
  classical
  rw [mem_conormalForms] at hβ
  ext v
  rw [AlternatingMap.curryLeft_apply_apply, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ]
  have hz (a : Fin k) : β (a.succ.removeNth (Matrix.vecCons n v)) = 0 := by
    have : NeZero k := ⟨by have := a.isLt; omega⟩
    exact hβ _ 0 (by simpa [Fin.removeNth, Fin.succAbove_of_castSucc_lt] using hn)
  simp [hz]

end Submodule

namespace Submodule

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M] {k : ℕ}
  {U W : Submodule R M}

/-- The covector wedge is nonzero when its covector is nonzero on the tangent space. -/
theorem alternatizeUncurryFin_smulRight_ne_zero {α : M [⋀^Fin k]→ₗ[R] R}
    (hα : α ∈ W.conormalForms (Fin k)) (hα0 : α ≠ 0) (l : M →ₗ[R] R)
    (hl : ∃ n ∈ W, l n ≠ 0) :
    AlternatingMap.alternatizeUncurryFin (l.smulRight α) ≠ 0 := by
  obtain ⟨n, hn, hln⟩ := hl
  intro hz
  have he := Submodule.curryLeft_alternatizeUncurryFin_smulRight_of_mem hα l hn
  rw [hz, AlternatingMap.curryLeft_zero, LinearMap.zero_apply] at he
  exact (smul_ne_zero hln hα0) he.symm

end Submodule

namespace Module.Ray

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] {k : ℕ} {W U : Submodule R M}

/-- Prepend a covector to a conormal orientation. Its restriction to the tangent
space must be nonzero. -/
noncomputable def wedgeCovector (o : Module.Ray R (M [⋀^Fin k]→ₗ[R] R))
    (ho : o.IsConormal W) (l : M →ₗ[R] R) (hl : ∃ n ∈ W, l n ≠ 0) :
    Module.Ray R (M [⋀^Fin (k + 1)]→ₗ[R] R) :=
  rayOfNeZero R (AlternatingMap.alternatizeUncurryFin (l.smulRight o.someVector))
    (Submodule.alternatizeUncurryFin_smulRight_ne_zero
      ((isConormal_rayOfNeZero_iff o.someVector_ne_zero).mp (o.someVector_ray.symm ▸ ho))
      o.someVector_ne_zero l hl)

/-- Compute the covector wedge using any representing form. -/
@[simp]
theorem wedgeCovector_rayOfNeZero {α : M [⋀^Fin k]→ₗ[R] R} (hα : α ≠ 0)
    (ho : (rayOfNeZero R α hα).IsConormal W) (l : M →ₗ[R] R)
    (hl : ∃ n ∈ W, l n ≠ 0) :
    (rayOfNeZero R α hα).wedgeCovector ho l hl =
      rayOfNeZero R (AlternatingMap.alternatizeUncurryFin (l.smulRight α))
        (Submodule.alternatizeUncurryFin_smulRight_ne_zero
          ((isConormal_rayOfNeZero_iff hα).mp ho) hα l hl) := by
  apply (ray_eq_iff _ _).mpr
  exact ((ray_eq_iff (Module.Ray.someVector_ne_zero _) hα).mp
    (Module.Ray.someVector_ray _)).map
      (AlternatingMap.alternatizeUncurryFinLM.comp (LinearMap.smulRightₗ l))

/-- The covector wedge is conormal to any subspace annihilated by both factors. -/
theorem isConormal_wedgeCovector (o : Module.Ray R (M [⋀^Fin k]→ₗ[R] R))
    (ho : o.IsConormal W) (l : M →ₗ[R] R) (hl : ∃ n ∈ W, l n ≠ 0)
    (hUW : U ≤ W) (hUl : U ≤ l.ker) :
    (o.wedgeCovector ho l hl).IsConormal U := by
  rw [wedgeCovector, isConormal_rayOfNeZero_iff, Submodule.mem_conormalForms]
  intro v j hv
  exact Submodule.mem_conormalForms.mp
    (Submodule.conormalForms_alternatizeUncurryFin_smulRight
      ((isConormal_rayOfNeZero_iff o.someVector_ne_zero).mp (o.someVector_ray.symm ▸ ho)) l)
    v j ⟨hUW hv, hUl hv⟩

/-- Contracting a covector wedge along a positive tangent vector recovers the
original orientation. -/
theorem contract_wedgeCovector (o : Module.Ray R (M [⋀^Fin k]→ₗ[R] R))
    (ho : o.IsConormal W) (l : M →ₗ[R] R) (hl : ∃ n ∈ W, l n ≠ 0)
    (hUW : U ≤ W) (hUl : U ≤ l.ker) (hk : Module.finrank R (M ⧸ U) = k + 1)
    {n : M} (hn : n ∈ W) (hln : 0 < l n) :
    (o.wedgeCovector ho l hl).contract
      (o.isConormal_wedgeCovector ho l hl hUW hUl) hk n
      (fun hu => (ne_of_gt hln) (LinearMap.mem_ker.mp (hUl hu))) = o := by
  induction o using Module.Ray.ind with
  | h α hα =>
    simp only [wedgeCovector_rayOfNeZero, contract_rayOfNeZero]
    have he := Submodule.curryLeft_alternatizeUncurryFin_smulRight_of_mem
      ((isConormal_rayOfNeZero_iff hα).mp ho) l hn
    apply (ray_eq_iff _ _).mpr
    rw [he]
    exact SameRay.sameRay_pos_smul_left α hln

/-- Reversing the orientation reverses its covector wedge. -/
@[simp]
theorem wedgeCovector_neg (o : Module.Ray R (M [⋀^Fin k]→ₗ[R] R))
    (ho : o.IsConormal W) (l : M →ₗ[R] R) (hl : ∃ n ∈ W, l n ≠ 0) :
    (-o).wedgeCovector (isConormal_neg_iff.mpr ho) l hl = -o.wedgeCovector ho l hl := by
  induction o using Module.Ray.ind with
  | h α hα =>
    simp only [neg_rayOfNeZero, wedgeCovector_rayOfNeZero]
    apply (ray_eq_iff _ _).mpr
    have he : l.smulRight (-α) = -(l.smulRight α) := by ext n v; simp
    rw [he, ← neg_one_smul R (l.smulRight α), AlternatingMap.alternatizeUncurryFin_smul]
    simp

end Module.Ray
