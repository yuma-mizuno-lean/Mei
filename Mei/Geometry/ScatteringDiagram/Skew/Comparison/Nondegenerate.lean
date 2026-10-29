/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Comparison.Basic

/-!
# Nondegenerate skew comparison

For a nondegenerate integral skew form, the real comparison with the continuous
dual is a linear equivalence. Thus a codimension-one rational-normal cone in a degree
evaluation hyperplane pulls back to a nonempty rational-normal support of codimension one,
with direction the kernel of the normalized integral skew normal. The normal
has the same sign as evaluation after comparison, so the two descriptions give
the same signed crossing factors. Recession membership is the incomingness test
already established for arbitrary skew forms.

Pullback preserves the dimension of the affine direction of every set, including
the empty set. This transports codimension hypotheses on the original support
to its pullback. The geometric comparison
follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1 and Appendix B, and Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, Remark 2.3.
-/

public section
noncomputable section

open Set

namespace Mei.SkewLatticeDatum

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (D : SkewLatticeDatum N) (hD : ∀ a b, ∃ k : ℤ, D.form a b = k)
  {i : N →+ V} (h : TauCeti.Toric.IsIntegralLattice i)

/-- Nondegeneracy of the integral form makes real skew comparison bijective. -/
theorem skewComparison_bijective (hnd : D.form.Nondegenerate) :
    Function.Bijective (D.skewComparison hD h) := by
  let := h.finiteDimensional
  have he := h.eq_extend (i' := h.continuousRealCharacter)
    (f := LinearMap.toAddMonoidHom'.comp (D.integralCharacter hD).toAddMonoidHom)
    (D.skewComparison_lattice hD h)
  have hi : Function.Injective (D.skewComparison hD h) := by
    rw [he]
    apply h.extend_injective h.continuousDual
    intro x y hxy
    exact D.integralCharacter_injective hD hnd.1 (LinearMap.toAddMonoidHom_injective hxy)
  have hd : Module.finrank ℝ V = Module.finrank ℝ (V →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : Module.Dual ℝ V ≃ₗ[ℝ]
      (V →L[ℝ] ℝ)).finrank_eq, Subspace.dual_finrank_eq]
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

/-- The real skew comparison as a linear equivalence for a nondegenerate form. -/
def skewComparisonEquiv (hnd : D.form.Nondegenerate) : V ≃ₗ[ℝ] (V →L[ℝ] ℝ) :=
  LinearEquiv.ofBijective (D.skewComparison hD h) (D.skewComparison_bijective hD h hnd)

/-- The equivalence retains the original comparison map. -/
@[simp]
theorem skewComparisonEquiv_toLinearMap (hnd : D.form.Nondegenerate) :
    (D.skewComparisonEquiv hD h hnd).toLinearMap = D.skewComparison hD h := (rfl)

/-- Evaluation of the equivalence is the original skew comparison. -/
@[simp]
theorem coe_skewComparisonEquiv (hnd : D.form.Nondegenerate) :
    ⇑(D.skewComparisonEquiv hD h hnd) = D.skewComparison hD h := (rfl)

/-- Comparison recovers a dual vector from its inverse image. -/
@[simp]
theorem skewComparison_skewComparisonEquiv_symm (hnd : D.form.Nondegenerate)
    (θ : V →L[ℝ] ℝ) :
    D.skewComparison hD h ((D.skewComparisonEquiv hD h hnd).symm θ) = θ :=
  (D.skewComparisonEquiv hD h hnd).apply_symm_apply θ

/-- The inverse comparison recovers an original vector. -/
@[simp]
theorem skewComparisonEquiv_symm_skewComparison (hnd : D.form.Nondegenerate) (x : V) :
    (D.skewComparisonEquiv hD h hnd).symm (D.skewComparison hD h x) = x :=
  (D.skewComparisonEquiv hD h hnd).symm_apply_apply x

/-- Pullback preserves the dimension of the affine direction of every set,
including the empty set. -/
theorem finrank_direction_skewComparison_preimage (hnd : D.form.Nondegenerate)
    (σ : Set (V →L[ℝ] ℝ)) :
    Module.finrank ℝ (affineSpan ℝ ((D.skewComparison hD h) ⁻¹' σ)).direction =
      Module.finrank ℝ (affineSpan ℝ σ).direction := by
  let e := D.skewComparisonEquiv hD h hnd
  have he : (D.skewComparison hD h) ⁻¹' σ = e.symm.toAffineEquiv.toAffineMap '' σ :=
    (e.toEquiv.image_symm_eq_preimage σ).symm
  rw [he, ← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact e.symm.finrank_map_eq _

/-- For a nondegenerate form, the pullback of a codimension-one subset of a
degree hyperplane has the required normalized-normal direction. -/
theorem direction_skewComparison_preimage_of_nondegenerate
    (hnd : D.form.Nondegenerate) {n : N} (hn : n ∈ D.unfrozen) (hn0 : n ≠ 0)
    (σ : Set (V →L[ℝ] ℝ)) (hσ : ∀ θ ∈ σ, θ (i n) = 0)
    (hcodim : Module.finrank ℝ (affineSpan ℝ σ).direction + 1 =
      Module.finrank ℝ (V →L[ℝ] ℝ)) :
    let _ := h.free
    (affineSpan ℝ ((D.skewComparison hD h) ⁻¹' σ)).direction =
      LinearMap.ker (h.realCharacter (D.normal n hn).toAddMonoidHom) := by
  let := h.free
  apply D.direction_skewComparison_preimage hD h hn σ hσ (D.normal_ne_zero hnd.2 hn hn0)
  rw [D.finrank_direction_skewComparison_preimage hD h hnd, hcodim]
  exact (D.skewComparisonEquiv hD h hnd).finrank_eq.symm

end Mei.SkewLatticeDatum
