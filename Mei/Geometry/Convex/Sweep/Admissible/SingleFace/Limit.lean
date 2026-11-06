/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace.Domain
public import Mei.Geometry.Convex.Sweep.Admissible.Limit

/-!
# Closed paths through a single face

The continuous hinge extension of a one-crossing path retains its computed
crossing point at every endpoint. This point lies on the face when `ν w ≠ 0`;
otherwise the formula is totalized. At a terminal crossing its negative half-line
is exactly the incoming affine line. The formulas in
`Mei.Geometry.Convex.Sweep.Degeneration` include unchanged spatial directions
and singular crossings.

The boundary of the admissible endpoint domain is realized on these same paths:
every excluded limiting endpoint is terminal or has a negative-time singular
crossing, even when the singular subset is nonclosed. No boundary admissibility
is asserted. We combine the existing single-face domain classification with
`backwardPath`; this is the closed-chart interpretation of Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (ν : V →L[ℝ] ℝ) (b : ℝ) (u w : V)

variable {ν b u w} {Z : Set V}

/-- Every excluded limiting endpoint is a terminal crossing or an actual
negative-time singular contact of the continuous path extension. This necessary
boundary condition does not require the singular subset to be closed or dense. -/
theorem backwardPath_singleFace_boundary
    (hn : ν w = ν u) (hZ : Z ⊆ {x | ν x = b})
    {Q : V}
    (hQ : Q ∈ closure (admissibleBackwardDomain
      (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν u}))
    (hnot : Q ∉ admissibleBackwardDomain
      (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν u}) :
    ν Q = b ∨ ((ν Q - b) / ν w < 0 ∧
      backwardPath (fun _ : Fin 1 => ν) (fun _ => b) ![w, u] Q
        ((ν Q - b) / ν w) ∈ Z) := by
  obtain ⟨X, hX⟩ := (Set.nonempty_of_mem hQ).of_closure
  obtain ⟨r⟩ := (nonempty_admissibleRayRealization_iff ..).mpr hX
  have hw : ν w ≠ 0 := r.transverse 0
  have ht : (ν Q - b) / ν w ≤ 0 :=
    closure_minimal (fun x hx =>
      ((mem_admissibleBackwardDomain_singleFace_one_iff hn hZ).mp hx).1.le)
      (isClosed_le ((ν.continuous.sub continuous_const).div_const _) continuous_const) hQ
  rcases ht.lt_or_eq with ht | ht
  · right
    refine ⟨ht, ?_⟩
    have hx := (mem_admissibleBackwardDomain_singleFace_one_iff hn hZ).not.mp hnot
    rw [backwardPath_singleFace_crossing, ← sweepProjection_inv_smul_apply]
    tauto
  · exact Or.inl (sub_eq_zero.mp ((div_eq_zero_iff.mp ht).resolve_right hw))

end Mei.Convex
