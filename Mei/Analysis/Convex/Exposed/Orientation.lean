/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Exposed
public import Mei.LinearAlgebra.Alternating.Extension

/-!
# Conormal orientations of exposed facets

A conormally oriented set induces a conormal orientation on each exposed facet.
Append its outward conormal to the parent conormal frame and multiply by
`(-1)^(k+1)` in parent codimension `k`. Equivalently, negate the wedge with the
outward covector placed first. Contraction along any outward tangent vector
then recovers the negative parent orientation. This characterizes the facet
orientation and makes it independent of ambient covector extensions.

The construction extends `IsExposed.outwardNormal` using
`LinearMap.exists_extend` and uses `Module.Ray.wedgeCovector` for the wedge.
-/

public section

noncomputable section

namespace IsExposed

open Module

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  {P F : Set V} {k : ℕ} [FiniteDimensional K (vectorSpan K P)]

private def facetCovector (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P)) : V →ₗ[K] K :=
  ((hF.outwardNormal hne hdim).someVector.exists_extend).choose

omit [FiniteDimensional K (vectorSpan K P)] in
private theorem facetCovector_comp (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P)) :
    (facetCovector hF hne hdim).comp (vectorSpan K P).subtype =
      (hF.outwardNormal hne hdim).someVector :=
  ((hF.outwardNormal hne hdim).someVector.exists_extend).choose_spec

omit [FiniteDimensional K (vectorSpan K P)] in
private theorem facetCovector_nonzero (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P)) :
    ∃ n ∈ vectorSpan K P, facetCovector hF hne hdim n ≠ 0 := by
  by_contra hn
  apply (hF.outwardNormal hne hdim).someVector_ne_zero
  rw [← facetCovector_comp hF hne hdim]
  ext n
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply] using
    not_not.mp (fun hne => hn ⟨n, n.property, hne⟩)

private theorem facetCovector_annihilates (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P)) :
    vectorSpan K F ≤ (facetCovector hF hne hdim).ker := by
  intro n hn
  have hnP := vectorSpan_mono K hF.subset hn
  have hz : (hF.outwardNormal hne hdim).someVector ⟨n, hnP⟩ = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hF.ker_outwardNormal hne hdim]
    exact hn
  rw [← facetCovector_comp hF hne hdim] at hz
  exact hz

/-- The induced conormal orientation of an exposed facet: append the outward
conormal to the parent frame, with the coboundary sign `(-1)^(k+1)`.
Equivalently, prepend the outward covector and negate the result. -/
def facetOrientation (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P))
    (o : Module.Ray K (V [⋀^Fin k]→ₗ[K] K)) (ho : o.IsConormal (vectorSpan K P)) :
    Module.Ray K (V [⋀^Fin (k + 1)]→ₗ[K] K) :=
  -o.wedgeCovector ho (facetCovector hF hne hdim) (facetCovector_nonzero hF hne hdim)

/-- The facet orientation annihilates the direction of the facet. -/
theorem isConormal_facetOrientation (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P))
    (o : Module.Ray K (V [⋀^Fin k]→ₗ[K] K)) (ho : o.IsConormal (vectorSpan K P)) :
    (hF.facetOrientation hne hdim o ho).IsConormal (vectorSpan K F) := by
  rw [facetOrientation, Module.Ray.isConormal_neg_iff]
  exact o.isConormal_wedgeCovector ho _ _ (vectorSpan_mono K hF.subset)
    (facetCovector_annihilates hF hne hdim)

/-- Contraction along any outward tangent vector gives the negative parent
orientation, independently of the length of that vector. -/
theorem contract_facetOrientation (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P))
    (o : Module.Ray K (V [⋀^Fin k]→ₗ[K] K)) (ho : o.IsConormal (vectorSpan K P))
    (hk : finrank K (V ⧸ vectorSpan K F) = k + 1)
    (n : vectorSpan K P) (hn : 0 < (hF.outwardNormal hne hdim).someVector n) :
    (hF.facetOrientation hne hdim o ho).contract
      (hF.isConormal_facetOrientation hne hdim o ho) hk n
      (fun hnF => (ne_of_gt hn) (by
        apply LinearMap.mem_ker.mp
        rw [hF.ker_outwardNormal hne hdim]
        exact hnF)) = -o := by
  have hpos : 0 < facetCovector hF hne hdim n := by
    simpa only [← facetCovector_comp hF hne hdim, LinearMap.comp_apply,
      Submodule.subtype_apply] using hn
  simp only [facetOrientation]
  rw [Module.Ray.contract_neg _
    (o.isConormal_wedgeCovector ho _ _ (vectorSpan_mono K hF.subset)
      (facetCovector_annihilates hF hne hdim))]
  rw [Module.Ray.contract_wedgeCovector o ho _ _ (vectorSpan_mono K hF.subset)
    (facetCovector_annihilates hF hne hdim) hk n.property hpos]

/-- Contraction along one outward tangent vector characterizes the induced
facet orientation among conormal orientations of the facet. -/
theorem facetOrientation_eq_iff_contract (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P))
    (o : Module.Ray K (V [⋀^Fin k]→ₗ[K] K)) (ho : o.IsConormal (vectorSpan K P))
    (p : Module.Ray K (V [⋀^Fin (k + 1)]→ₗ[K] K)) (hp : p.IsConormal (vectorSpan K F))
    (hk : finrank K (V ⧸ vectorSpan K F) = k + 1)
    (n : vectorSpan K P) (hn : 0 < (hF.outwardNormal hne hdim).someVector n) :
    hF.facetOrientation hne hdim o ho = p ↔
      p.contract hp hk n (fun hnF => (ne_of_gt hn) (by
        apply LinearMap.mem_ker.mp
        rw [hF.ker_outwardNormal hne hdim]
        exact hnF)) = -o := by
  rw [← Module.Ray.contract_eq_contract_iff _ _
    (hF.isConormal_facetOrientation hne hdim o ho) hp hk n
    (fun hnF => (ne_of_gt hn) (by
      apply LinearMap.mem_ker.mp
      rw [hF.ker_outwardNormal hne hdim]
      exact hnF)), hF.contract_facetOrientation hne hdim o ho hk n hn]
  exact eq_comm

omit [FiniteDimensional K (vectorSpan K P)] in
/-- Reversing the parent orientation reverses the induced facet orientation. -/
@[simp]
theorem facetOrientation_neg (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P))
    (o : Module.Ray K (V [⋀^Fin k]→ₗ[K] K)) (ho : o.IsConormal (vectorSpan K P)) :
    hF.facetOrientation hne hdim (-o) (Module.Ray.isConormal_neg_iff.mpr ho) =
      -hF.facetOrientation hne hdim o ho := by
  simp only [facetOrientation]
  rw [Module.Ray.wedgeCovector_neg o ho]

end IsExposed
