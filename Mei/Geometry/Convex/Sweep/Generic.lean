/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Topology
public import Mei.Geometry.Affine.IncomingGerm

/-!
# Generic straight incoming germs at backward intersections

Project an endpoint onto a hyperplane along an outgoing direction, then move a
short distance in a transverse incoming direction. One finite exceptional
arrangement of endpoints makes all these straight incoming germs generic for
any prescribed target arrangement. The same positive displacement bound works
for finitely many hyperplanes and direction pairs. In particular, the incoming
direction need not avoid every exceptional direction: an exception parallel to
it is avoided by excluding its proper affine preimage at the endpoint.

This lets backward-ray coefficient recursions evaluate smaller-degree inputs at
the actual straight cut points. No perturbation of a cut ray is necessary once
the endpoint arrangement has been refined. The intersection itself may lie in
the target discriminant, including when that discriminant contains the entire
crossing hyperplane.

For singular sets contained in affine subspaces that do not contain the crossing
hyperplane, `exists_forall_notMem_sweepProjection` instead excludes the singular
crossings themselves. Its endpoint exceptions are the affine preimages of those
subspaces under the sweep projections.

We use `sweepProjection` and
`ExceptionalArrangement.exists_forall_eventually_isGeneric_smul_vadd`. The
backward-ray application follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]

/-- One finite endpoint arrangement makes every projected crossing avoid each
of the given affine subspaces. Each subspace must miss some point of each
crossing hyperplane. Sweeping vectors need not be normalized or transverse. -/
theorem exists_forall_notMem_sweepProjection {κ : Type*} [Finite κ]
    (f : ι → V →L[ℝ] ℝ) (c : ι → ℝ) (n : ι → V)
    (A : κ → AffineSubspace ℝ V)
    (hA : ∀ j l, ∃ x, f j x = c j ∧ x ∉ A l) :
    ∃ E : ExceptionalArrangement V, ∀ Q, E.IsGeneric Q →
      ∀ j l, sweepProjection (f j) (c j) (n j) Q ∉ A l := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let B (z : ι × κ) := (A z.2).comap (sweepProjection (f z.1) (c z.1) (n z.1)).toAffineMap
  have hB (z : ι × κ) : B z ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx, hxA⟩ := hA z.1 z.2
    have hm := AffineSubspace.mem_comap.mp (htop ▸ AffineSubspace.mem_top ℝ V x)
    exact hxA (by simpa only [ContinuousAffineMap.coe_toAffineMap,
      sweepProjection_eq_self _ _ hx] using hm)
  let E : ExceptionalArrangement V :=
    ⟨Finset.univ.image B, fun _ hm => by
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hm
      exact hB z⟩
  refine ⟨E, fun Q hQ j l hm => ?_⟩
  exact (ExceptionalArrangement.isGeneric_iff.mp hQ) (B (j, l))
    (Finset.mem_image.mpr ⟨(j, l), Finset.mem_univ _, rfl⟩)
    (AffineSubspace.mem_comap.mpr hm)

/-- A finite refinement of endpoint exceptions makes every short incoming germ
at a projected crossing generic, simultaneously for a finite family. Only the
incoming normal velocities must be nonzero; sweeping vectors are arbitrary. -/
theorem exists_forall_eventually_isGeneric_sweepProjection
    (E : ExceptionalArrangement V) (f : ι → V →L[ℝ] ℝ) (c : ι → ℝ)
    (n v : ι → V) (hv : ∀ j, f j (v j) ≠ 0) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ j,
        E.IsGeneric (sweepProjection (f j) (c j) (n j) Q + t • v j) := by
  obtain ⟨F, hF⟩ := E.exists_forall_eventually_isGeneric_smul_vadd
    (fun j => (sweepProjection (f j) (c j) (n j)).toAffineMap) v
    (fun j => (f j).surjective_smul_add_sweepProjection (c j) (n j) (v j) (hv j))
  exact ⟨F, fun Q hQ => (hF Q hQ).mono fun t ht j => by
    simpa only [ContinuousAffineMap.coe_toAffineMap, vadd_eq_add, add_comm] using ht j⟩

end Mei.Convex
