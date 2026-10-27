/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted
public import Mei.LinearAlgebra.ModuleFiltration.Bilinear
public import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Products of shifted coefficient modules

In a graded algebra, multiplication carries the module supported on `p + P`
and the module supported on `q + P` to that supported on `(p + q) + P`.
It adds relative filtration orders, so it extends to their completions, even
when the ambient shifts have negative degree. The completed products are
bilinear, associative, and computed by products of quotient representatives.
These are the coefficient products used to multiply formal theta series.

We use `Mei.shiftedSubmodule`, the relative filtrations of shifted modules,
and `ModuleFiltration.completionBilinear`, built from Mathlib's quotient
bilinear maps. No commutativity of the coefficient algebra or freeness of its
homogeneous pieces is required.
-/

public section

noncomputable section

namespace Mei

section Semiring

variable {R A Γ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid Γ] (𝒜 : Γ → Submodule R A) [SetLike.GradedMul 𝒜]
  (P : AddSubmonoid Γ) (p q : Γ)

/-- Multiplication of modules supported on translates adds the shifts. -/
theorem shiftedSubmodule_mul_le :
    shiftedSubmodule 𝒜 P p * shiftedSubmodule 𝒜 P q ≤ shiftedSubmodule 𝒜 P (p + q) := by
  simp only [shiftedSubmodule_def, Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
  intro n m
  apply (TauCeti.GradedAlgebra.mul_le_grade_add 𝒜 (p + m) (q + n)).trans
  have he : p + m + (q + n) = p + q + (m + n : P) := by
    simp only [AddSubmonoid.coe_add]
    ac_rfl
  rw [he]
  simpa only [shiftedSubmodule_def, AddSubmonoid.coe_add] using
    le_shiftedSubmodule 𝒜 P (p + q) (P.add_mem m.property n.property)

/-- The bilinear product of two shifted coefficient modules. -/
def shiftedMul : shiftedSubmodule 𝒜 P p →ₗ[R]
    shiftedSubmodule 𝒜 P q →ₗ[R] shiftedSubmodule 𝒜 P (p + q) :=
  LinearMap.mk₂ R
    (fun x y => ⟨(x : A) * y, shiftedSubmodule_mul_le 𝒜 P p q
      (Submodule.mul_mem_mul x.property y.property)⟩)
    (by intros; apply Subtype.ext; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; exact smul_mul_assoc _ _ _)
    (by intros; apply Subtype.ext; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; exact mul_smul_comm _ _ _)

/-- The shifted product is the original product on underlying coefficients. -/
@[simp]
theorem coe_shiftedMul (x : shiftedSubmodule 𝒜 P p) (y : shiftedSubmodule 𝒜 P q) :
    (shiftedMul 𝒜 P p q x y : A) = (x : A) * y := (rfl)

end Semiring

namespace PositiveDegrees

section Semiring

variable {R A Γ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (𝒜 : Γ → Submodule R A) [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]
  (p q : Γ)

/-- Shifted multiplication adds relative filtration orders. -/
theorem shiftedMul_mem_shiftedFiltration {a b : ℕ}
    {x : shiftedSubmodule 𝒜 d.monoid p} {y : shiftedSubmodule 𝒜 d.monoid q}
    (hx : x ∈ (d.shiftedFiltration 𝒜 p).submodule a)
    (hy : y ∈ (d.shiftedFiltration 𝒜 q).submodule b) :
    shiftedMul 𝒜 d.monoid p q x y ∈ (d.shiftedFiltration 𝒜 (p + q)).submodule (a + b) := by
  classical
  rw [d.mem_shiftedFiltration_iff 𝒜 p] at hx
  rw [d.mem_shiftedFiltration_iff 𝒜 q] at hy
  rw [d.mem_shiftedFiltration_iff 𝒜 (p + q)]
  intro r hr
  rw [coe_shiftedMul, ← DirectSum.sum_support_decompose 𝒜 (x : A),
    ← DirectSum.sum_support_decompose 𝒜 (y : A), Finset.sum_mul]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.mul_sum]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : d.degree (i - p) < a
  · rw [hx i hi]
    simp
  by_cases hj : d.degree (j - q) < b
  · rw [hy j hj]
    simp
  apply DirectSum.decompose_of_mem_ne 𝒜
    (SetLike.mul_mem_graded (DirectSum.decompose 𝒜 (x : A) i).property
      (DirectSum.decompose 𝒜 (y : A) j).property)
  intro he
  have hd : d.degree (r - (p + q)) = d.degree (i - p) + d.degree (j - q) := by
    rw [← he, map_sub, map_add, map_add, map_sub, map_sub]
    ring
  have hab := add_le_add (le_of_not_gt hi) (le_of_not_gt hj)
  omega

end Semiring

variable {R A Γ : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (𝒜 : Γ → Submodule R A) [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]
  (p q : Γ)

/-- Products of completed shifted coefficients, with shifts added. -/
def shiftedCompletionMul : d.ShiftedCoefficients 𝒜 p →ₗ[R]
    d.ShiftedCoefficients 𝒜 q →ₗ[R] d.ShiftedCoefficients 𝒜 (p + q) :=
  ModuleFiltration.completionBilinear
    (d.shiftedFiltration 𝒜 p) (d.shiftedFiltration 𝒜 q) (d.shiftedFiltration 𝒜 (p + q))
    (shiftedMul 𝒜 d.monoid p q)
    (fun _ _ _ _ => d.shiftedMul_mem_shiftedFiltration 𝒜 p q)

/-- Products of representatives compute each projection of a completed product. -/
theorem projection_shiftedCompletionMul (k : ℕ)
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q)
    (u : shiftedSubmodule 𝒜 d.monoid p) (v : shiftedSubmodule 𝒜 d.monoid q)
    (hu : Submodule.Quotient.mk u = (d.shiftedFiltration 𝒜 p).projection k x)
    (hv : Submodule.Quotient.mk v = (d.shiftedFiltration 𝒜 q).projection k y) :
    (d.shiftedFiltration 𝒜 (p + q)).projection k (d.shiftedCompletionMul 𝒜 p q x y) =
      Submodule.Quotient.mk (shiftedMul 𝒜 d.monoid p q u v) := by
  rw [shiftedCompletionMul, ModuleFiltration.projection_completionBilinear, ← hu, ← hv,
    ModuleFiltration.quotientBilinear_mk]

/-- Original coefficients multiply before or after passage to the completion. -/
@[simp]
theorem shiftedCompletionMul_of
    (x : shiftedSubmodule 𝒜 d.monoid p) (y : shiftedSubmodule 𝒜 d.monoid q) :
    d.shiftedCompletionMul 𝒜 p q
      ((d.shiftedFiltration 𝒜 p).of x) ((d.shiftedFiltration 𝒜 q).of y) =
      (d.shiftedFiltration 𝒜 (p + q)).of (shiftedMul 𝒜 d.monoid p q x y) :=
  ModuleFiltration.completionBilinear_of _ _ _ _ _ x y

/-- Completed products add relative orders, including order zero. -/
theorem shiftedCompletionMul_mem_completedFiltration {a b : ℕ}
    {x : d.ShiftedCoefficients 𝒜 p} {y : d.ShiftedCoefficients 𝒜 q}
    (hx : x ∈ (d.shiftedFiltration 𝒜 p).completedFiltration.submodule a)
    (hy : y ∈ (d.shiftedFiltration 𝒜 q).completedFiltration.submodule b) :
    d.shiftedCompletionMul 𝒜 p q x y ∈
      (d.shiftedFiltration 𝒜 (p + q)).completedFiltration.submodule (a + b) :=
  ModuleFiltration.completionBilinear_mem_completedFiltration _ _ _ _ _ hx hy

omit [DecidableEq Γ] [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜] in
private theorem projection_cast {s t : Γ} (h : s = t)
    (x : d.ShiftedCoefficients 𝒜 s) (k : ℕ) :
    (d.shiftedFiltration 𝒜 t).projection k
        (cast (congrArg (d.ShiftedCoefficients 𝒜) h) x) =
      cast (congrArg (fun s => (d.shiftedFiltration 𝒜 s).quotient k) h)
        ((d.shiftedFiltration 𝒜 s).projection k x) := by
  subst t
  rfl

omit [DecidableEq Γ] [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜] in
private theorem quotient_cast_mk {s t : Γ} (h : s = t)
    (x : shiftedSubmodule 𝒜 d.monoid s) (k : ℕ) :
    cast (congrArg (fun s => (d.shiftedFiltration 𝒜 s).quotient k) h)
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨(x : A), by simpa only [← h] using x.property⟩ : shiftedSubmodule 𝒜 d.monoid t) := by
  subst t
  rfl

/-- Completed shifted products are associative after identifying the equal total shifts. -/
theorem shiftedCompletionMul_assoc (r : Γ)
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q)
    (z : d.ShiftedCoefficients 𝒜 r) :
    cast (congrArg (d.ShiftedCoefficients 𝒜) (add_assoc p q r))
        (d.shiftedCompletionMul 𝒜 (p + q) r (d.shiftedCompletionMul 𝒜 p q x y) z) =
      d.shiftedCompletionMul 𝒜 p (q + r) x (d.shiftedCompletionMul 𝒜 q r y z) := by
  apply (d.shiftedFiltration 𝒜 (p + (q + r))).completion_ext
  intro k
  obtain ⟨u, hu⟩ := ((d.shiftedFiltration 𝒜 p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 p).projection k x)
  obtain ⟨v, hv⟩ := ((d.shiftedFiltration 𝒜 q).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 q).projection k y)
  obtain ⟨w, hw⟩ := ((d.shiftedFiltration 𝒜 r).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 r).projection k z)
  have huv := d.projection_shiftedCompletionMul 𝒜 p q k x y u v hu hv
  have hvw := d.projection_shiftedCompletionMul 𝒜 q r k y z v w hv hw
  rw [projection_cast d 𝒜 (add_assoc p q r), d.projection_shiftedCompletionMul 𝒜 (p + q) r k _ _
      (shiftedMul 𝒜 d.monoid p q u v) w huv.symm hw,
    d.projection_shiftedCompletionMul 𝒜 p (q + r) k _ _
      u (shiftedMul 𝒜 d.monoid q r v w) hu hvw.symm,
    quotient_cast_mk d 𝒜 (add_assoc p q r)]
  congr 1
  apply Subtype.ext
  simp only [coe_shiftedMul]
  exact mul_assoc (u : A) v w

end PositiveDegrees
end Mei
