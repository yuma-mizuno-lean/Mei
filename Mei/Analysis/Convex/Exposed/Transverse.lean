/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Exposed
public import Mei.LinearAlgebra.AffineSpace.Halfspace

/-!
# Inward rays transverse to exposed facets

For an exposed facet and a point `p` on it, the supporting half-space inside
the parent's affine span intersects a complement of the facet direction in
one inward ray from `p`. The result identifies the slice of the supporting
half-space, rather than asserting that an arbitrary parent set equals that
half-space. For polyhedra a local half-space model therefore turns this ray
into the local wall slice used in transverse intersection calculations.

The facet kernel computation is
`ContinuousLinearMap.ker_comp_vectorSpan_of_toExposed`. The ray parametrization
uses `AffineSubspace.exists_transverse_halfspace_ray`.
-/

public section

open Set Module

namespace ContinuousLinearMap

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  {P : Set V} [FiniteDimensional K (vectorSpan K P)]

/-- The supporting half-space of an exposed facet, restricted to a complement
of the facet direction, is a single inward ray from any point of the facet.
Only the parent's direction must be finite-dimensional. The parent need not
be convex, closed, full-dimensional or polyhedral. -/
theorem exists_transverse_halfspace_ray_of_toExposed (l : V →L[K] K)
    {p : V} (hp : p ∈ l.toExposed P)
    (hdim : finrank K (vectorSpan K (l.toExposed P)) + 1 = finrank K (vectorSpan K P))
    (T : Submodule K V) (hcompl : IsCompl (vectorSpan K (l.toExposed P)) T) :
    ∃ u ∈ vectorSpan K P ⊓ T, l u = -1 ∧
      ∀ z : V, (z - p ∈ T ∧ z ∈ affineSpan K P ∧ l z ≤ l p) ↔
        ∃ t : K, 0 ≤ t ∧ z = p + t • u := by
  have hne : (l.toExposed P).Nonempty := ⟨p, hp⟩
  have hproper : l.toExposed P ≠ P := by
    intro he
    rw [he] at hdim
    omega
  have hker : vectorSpan K P ⊓ l.toLinearMap.ker =
      vectorSpan K (l.toExposed P) := by
    apply le_antisymm
    · intro v hv
      have hm : (⟨v, hv.1⟩ : vectorSpan K P) ∈
          (l.toLinearMap.comp (vectorSpan K P).subtype).ker := hv.2
      rw [l.ker_comp_vectorSpan_of_toExposed hne hdim] at hm
      exact hm
    · exact le_inf (vectorSpan_mono K (fun _ hx => hx.1))
        (l.vectorSpan_toExposed_le_ker P)
  have hf : l.toLinearMap.domRestrict (vectorSpan K P) ≠ 0 :=
    l.comp_vectorSpan_ne_zero hne hproper
  simpa only [direction_affineSpan, ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub,
    sub_nonpos, vadd_eq_add, add_comm] using
    (affineSpan K P).exists_transverse_halfspace_ray l.toLinearMap
      (subset_affineSpan K P hp.1) T (by rw [direction_affineSpan]; exact hf)
      (by simpa only [direction_affineSpan, hker] using hcompl)

end ContinuousLinearMap
