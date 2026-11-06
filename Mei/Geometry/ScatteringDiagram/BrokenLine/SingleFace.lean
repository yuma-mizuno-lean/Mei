/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace

/-!
# Single-face encounter bounds for decorated rays

The normal-velocity equations of whole-component propagation imply that a
decorated ray meeting one face records at most one encounter. This conclusion
does not require positivity of coefficient degrees, a finite grading, or
nonzero geometric bends. In particular unchanged-degree encounters remain
counted, and degree changes invisible in space do not affect the bound.

For a full face in the obstacle family, the sign of the endpoint's normal
coordinate relative to the incoming normal velocity determines whether the
ray has zero or one encounter. The geometry, source and singular avoidance
are those of the existing `DecoratedAdmissibleRay` carrier. These are the
single-face bounds used before enumerating the surviving transfer components.

The proofs apply the single-face theorems for `AdmissibleRayRealization` to
`DecoratedAdmissibleRay.normal_velocity_eq`. Whole-component propagation is
as in Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p : Γ} {a : ℳ p} {v : Γ → V}
  {ν : V →L[ℝ] ℝ} {b : ℝ} {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : DecoratedAdmissibleRay ℳ T p a v (fun _ => ν) (fun _ => b) ε P W S C Q)

include r

/-- All segment degrees have the incoming normal velocity for a single face.
Only the normal component is asserted to agree. -/
theorem normal_velocity_eq_incoming_singleFace (i : Fin (n + 1)) :
    ν (v (Fin.snoc (α := fun _ => Γ) r.1.val p i)) = ν (v p) := by
  by_cases hi : i = Fin.last n
  · simp only [hi, Fin.snoc_last]
  · have he := (Fin.liftFun_iff_succ (· = ·)
      (f := fun i => ν (v (Fin.snoc (α := fun _ => Γ) r.1.val p i)))).mpr
      (fun j => by simpa only [Fin.snoc_castSucc] using r.normal_velocity_eq j)
      (Fin.lt_last_iff_ne_last.mpr hi)
    simpa only [Fin.snoc_last] using he

/-- Whole-component decorated rays through one face have at most one recorded
encounter, even if that encounter changes neither degree nor spatial velocity. -/
theorem encounter_count_le_one_singleFace : n ≤ 1 :=
  r.2.encounter_count_le_one_singleFace (fun j => by
    simpa only [Fin.snoc_castSucc] using r.normal_velocity_eq j)

/-- For a full face, the unique possible encounter occurs exactly on the side
opposite the incoming normal velocity. Source and singular constraints remain
in the decorated-ray hypothesis. -/
theorem encounter_count_eq_one_iff_singleFace
    (j : J) (hW : {x | ν x = b} ⊆ W j) :
    n = 1 ↔ (ν Q - b) / ν (v p) < 0 := by
  have he := r.2.encounter_count_eq_one_iff_singleFace
    (fun j => by simpa only [Fin.snoc_castSucc] using r.normal_velocity_eq j)
    j hW
  simpa only [r.normal_velocity_eq_incoming_singleFace] using he

end Mei.DecoratedAdmissibleRay
