/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Separation inside an affine span

A nonempty convex set can be weakly separated from a nonempty convex subset of
its affine span that misses its relative interior. The separating functional is
nonconstant on the first set, even when its affine span is a proper subspace of
the ambient space. This is useful for comparing supporting faces of adjacent
lower-dimensional cells.

The construction applies Mathlib's `geometric_hahn_banach_of_nonempty_interior`
in coordinates on the affine span, then uses `LinearMap.exists_extend` to extend
the resulting functional to the finite-dimensional ambient space. The affine-span
coordinates follow Mathlib's `Set.Nonempty.intrinsicInterior`.
-/

public section

open Set Module

namespace Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {P Q : Set V}

/-- Weak separation in the affine span, by a functional nonconstant on the first
set. The second set need only be contained in that affine span. -/
theorem exists_separating_of_disjoint_intrinsicInterior (hP : Convex ℝ P)
    (hQ : Convex ℝ Q) (hneP : P.Nonempty) (hneQ : Q.Nonempty)
    (hPQ : Q ⊆ affineSpan ℝ P) (hdisj : Disjoint (intrinsicInterior ℝ P) Q) :
    ∃ (l : V →L[ℝ] ℝ) (c : ℝ),
      l.toLinearMap.comp (vectorSpan ℝ P).subtype ≠ 0 ∧
        (∀ x ∈ P, l x ≤ c) ∧ ∀ y ∈ Q, c ≤ l y := by
  classical
  obtain ⟨q, hq⟩ := hneP
  let A := affineSpan ℝ P
  let qA : A := ⟨q, subset_affineSpan ℝ P hq⟩
  let : Nonempty A := ⟨qA⟩
  let : Nonempty P := ⟨⟨q, hq⟩⟩
  let e := AffineIsometryEquiv.vaddConst ℝ qA
  let a : A.direction →ᵃ[ℝ] V := A.subtype.comp e.toAffineEquiv.toAffineMap
  have ha (v : A.direction) : a v = (v : V) + q := rfl
  have hconvP : Convex ℝ (a ⁻¹' P) := hP.affine_preimage a
  have hconvQ : Convex ℝ (a ⁻¹' Q) := hQ.affine_preimage a
  -- On the direction space, the first set has nonempty ordinary interior.
  have hint : (interior (a ⁻¹' P)).Nonempty := by
    apply hconvP.interior_nonempty_iff_affineSpan_eq_top.mpr
    -- Expose the composite chart to apply the standard preimage and span lemmas.
    rw [show ⇑a = (Subtype.val : A → V) ∘ e.toAffineEquiv from rfl,
      preimage_comp, ← AffineSubspace.comap_span, affineSpan_coe_preimage_eq_top,
      AffineSubspace.comap_top]
  have hdisj' : Disjoint (interior (a ⁻¹' P)) (a ⁻¹' Q) := by
    apply Set.disjoint_left.mpr
    intro v hvP hvQ
    have hv : a v ∈ intrinsicInterior ℝ P := by
      apply mem_intrinsicInterior.mpr
      refine ⟨e v, ?_, rfl⟩
      -- The chart homeomorphism identifies relative interior with ordinary interior.
      rw [show (a ⁻¹' P) = e.toHomeomorph ⁻¹' ((↑) ⁻¹' P : Set A) from rfl,
        ← e.toHomeomorph.preimage_interior] at hvP
      exact hvP
    exact Set.disjoint_left.mp hdisj hv hvQ
  have hQne : (a ⁻¹' Q).Nonempty := by
    obtain ⟨x, hx⟩ := hneQ
    refine ⟨⟨x - q, A.vsub_mem_direction (hPQ hx) qA.property⟩, ?_⟩
    simpa only [mem_preimage, ha, sub_add_cancel] using hx
  obtain ⟨f, c, hf, hfP, hfQ⟩ :=
    geometric_hahn_banach_of_nonempty_interior hconvP hconvQ hdisj' hint hQne
  -- Extend the linear functional, absorbing the coordinate origin into the cutoff.
  obtain ⟨g, hg⟩ := f.toLinearMap.exists_extend
  let l : V →L[ℝ] ℝ := ⟨g, g.continuous_of_finiteDimensional⟩
  have hl (v : A.direction) : l v = f v := DFunLike.congr_fun hg v
  refine ⟨l, c + l q, ?_, ?_, ?_⟩
  · intro hz
    apply hf
    ext v
    have hv : (v : V) ∈ vectorSpan ℝ P := by
      simpa only [A, direction_affineSpan] using v.property
    have he := DFunLike.congr_fun hz ⟨v, hv⟩
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      ContinuousLinearMap.coe_coe, zero_apply, hl] using he
  · intro x hx
    let v : A.direction :=
      ⟨x - q, A.vsub_mem_direction (subset_affineSpan ℝ P hx) qA.property⟩
    have hv : v ∈ a ⁻¹' P := by
      rw [mem_preimage, ha]
      simpa only [v, sub_add_cancel] using hx
    have he := hfP v hv
    rw [← hl] at he
    simpa only [v, map_sub, sub_le_iff_le_add] using he
  · intro x hx
    let v : A.direction := ⟨x - q, A.vsub_mem_direction (hPQ hx) qA.property⟩
    have hv : v ∈ a ⁻¹' Q := by
      rw [mem_preimage, ha]
      simpa only [v, sub_add_cancel] using hx
    have he := hfQ v hv
    rw [← hl] at he
    simpa only [v, map_sub, le_sub_iff_add_le] using he

end Convex
