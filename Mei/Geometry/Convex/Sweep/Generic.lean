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

We use `sweepProjection` and
`ExceptionalArrangement.exists_forall_eventually_isGeneric_smul_vadd`. The
backward-ray application follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]

/-- A sweep projection followed by displacement in a transverse direction
covers the whole space. No condition on the sweeping vector is needed: the
projection fixes the hyperplane, and the displacement supplies its complement. -/
theorem _root_.ContinuousLinearMap.surjective_smul_add_sweepProjection
    (f : V →L[ℝ] ℝ) (c : ℝ) (n v : V)
    (hv : f v ≠ 0) :
    Function.Surjective (fun z : V × ℝ => z.2 • v + sweepProjection f c n z.1) := by
  intro y
  let t := (f y - c) / f v
  let x := y - t • v
  have hx : f x = c := by
    simp only [x, map_sub, map_smul, smul_eq_mul, t, div_mul_cancel₀ _ hv]
    ring
  refine ⟨(x, t), ?_⟩
  dsimp only
  rw [sweepProjection_eq_self f c hx]
  dsimp only [x]
  module

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
