/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Convex.Polyhedron.WallEvent
public import Mei.Geometry.Convex.Polyhedron.SingularSupport

/-!
# Canonical signed events of admissible rays

Replace a ray's chosen representative wall at each encounter by the complete
set of incident indexed walls and its chosen normal-velocity sign. The canonical
finite event alphabet distinguishes simultaneous encounters without losing
coincident wall indices. The path, every encounter parameter, local directions,
incoming source and singular avoidance are retained.

At a regular encounter all incident walls have the same affine direction.
Consequently the normal chosen by the event remains transverse even when it
differs from the original representative. This construction uses
`AdmissibleRayRealization` and `WallEvent`; simultaneous incidence follows
`affineSpan_eq_of_notMem_singularSupport`. The geometric conventions
are those of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set

namespace Mei.Convex.AdmissibleRayRealization

variable {V ι K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {n : ℕ} {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}
  {a : Fin n → ι} {v : Fin (n + 1) → V} {S : K → Set V} {C : Set V} {Q : V}
  (r : AdmissibleRayRealization (fun j => f (a j)) (fun j => c (a j)) v
    (fun j => W (a j)) W S C Q)

open Classical in
/-- At each recorded encounter, retain every incident indexed wall and the sign
of its chosen normal on the outgoing segment. -/
def wallEvents (j : Fin n) : WallEvent ι := by
  let s := (Set.toFinite {b | r.ray (r.parameter j.succ) ∈ W b}).toFinset
  have hs : s.Nonempty := ⟨a j, by simpa [s] using r.incidence j⟩
  exact (⟨s, hs⟩, SignType.sign (f hs.choose (v j.castSucc)))

/-- The canonical event retains exactly all walls containing the encounter point. -/
@[simp]
theorem mem_wallEvents (j : Fin n) (b : ι) :
    b ∈ (r.wallEvents j).1.val ↔ r.ray (r.parameter j.succ) ∈ W b := by
  classical
  simp [wallEvents]

/-- The sign carried by a canonical event is the actual normal-velocity sign. -/
@[simp↓]
theorem normal_sign_wallEvents (j : Fin n) :
    SignType.sign ((r.wallEvents j).normal f (v j.castSucc)) = (r.wallEvents j).2 := by
  simp [wallEvents]

/-- Canonical signed events do not depend on which incident representative wall
was originally recorded. Agreement of paths and encounter times suffices. -/
theorem wallEvents_eq_of_ray_eq_of_parameter_eq {a' : Fin n → ι}
    (s : AdmissibleRayRealization (fun j => f (a' j)) (fun j => c (a' j)) v
      (fun j => W (a' j)) W S C Q)
    (hr : r.ray = s.ray) (hp : r.parameter = s.parameter) : r.wallEvents = s.wallEvents := by
  funext j
  have hs : r.ray (r.parameter j.succ) ∈ (s.wallEvents j).support W := by
    rw [hr, hp]
    simp
  exact (r.wallEvents j).eq_of_mem_support_of_normal_sign_eq (s.wallEvents j) W f
    (v j.castSucc) (by simp) hs (r.normal_sign_wallEvents j) (s.normal_sign_wallEvents j)

variable (hker : ∀ b, (f b).toLinearMap.ker = (affineSpan ℝ (W b)).direction)
  (hregular : ∀ j : Fin n, r.ray (r.parameter j.succ) ∉ singularSupport W)

include hker hregular in
/-- Every incident wall is transverse at a regular recorded encounter, including
walls other than the original chosen representative. -/
theorem normal_ne_zero_of_mem_wallEvents (j : Fin n) {b : ι}
    (hb : b ∈ (r.wallEvents j).1.val) : f b (v j.castSucc) ≠ 0 := by
  have hb' := (r.mem_wallEvents j b).mp hb
  have hd : (affineSpan ℝ (W b)).direction = (affineSpan ℝ (W (a j))).direction :=
    congrArg AffineSubspace.direction
      (affineSpan_eq_of_notMem_singularSupport (hregular j) hb' (r.incidence j))
  intro hz
  apply r.transverse j
  have hm : v j.castSucc ∈ (affineSpan ℝ (W b)).direction := by
    rw [← hker b]
    exact LinearMap.mem_ker.mpr hz
  rwa [hd, ← hker (a j), LinearMap.mem_ker] at hm

variable (hW : ∀ b x, x ∈ W b → f b x = c b)

/-- Relabel all recorded encounters by their canonical signed simultaneous events.
The complete actual ray, parameter tuple and source conditions are preserved. -/
def withWallEvents :
    AdmissibleRayRealization (fun j => (r.wallEvents j).normal f)
      (fun j => (r.wallEvents j).offset c) v (fun j => (r.wallEvents j).support W)
      (fun e : WallEvent ι => e.support W) S C Q where
  ray := r.ray
  parameter := r.parameter
  parameter_zero := r.parameter_zero
  strictAnti_parameter := r.strictAnti_parameter
  transverse j := (r.wallEvents j).normal_ne_zero_of_mem_support W f
    (by simp) (fun b hb => r.normal_ne_zero_of_mem_wallEvents hker hregular j
      ((r.mem_wallEvents j b).mpr hb))
  endpoint_eq := r.endpoint_eq
  directionAt_eq := r.directionAt_eq
  bends_recorded := r.bends_recorded
  height_eq j := (r.wallEvents j).normal_apply_of_mem_support W f c hW
    (by simp)
  incidence j := by simp
  avoids_walls e t ht hne hm := r.avoids_walls _ t ht hne
    (e.support_subset W e.1.property.choose_spec hm)
  incoming := r.incoming
  avoids_singular := r.avoids_singular
  off_walls e hm := r.off_walls _ (e.support_subset W e.1.property.choose_spec hm)

/-- Canonical event relabelling preserves the entire path and incoming tail. -/
@[simp]
theorem ray_withWallEvents : (r.withWallEvents hker hregular hW).ray = r.ray := (rfl)

/-- Canonical event relabelling preserves all encounter times and the endpoint time. -/
@[simp]
theorem parameter_withWallEvents :
    (r.withWallEvents hker hregular hW).parameter = r.parameter := (rfl)

end Mei.Convex.AdmissibleRayRealization
