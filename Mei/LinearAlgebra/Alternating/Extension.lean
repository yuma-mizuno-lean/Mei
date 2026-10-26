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
