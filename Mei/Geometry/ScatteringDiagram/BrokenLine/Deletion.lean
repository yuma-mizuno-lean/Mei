/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Admissible.Deletion
public import Mei.LinearAlgebra.GradedModule.History.Erasure
public import Mei.Data.Fin.Tuple

/-!
# Deleting encounters that fix the whole decoration

Delete an encounter from an actual decorated admissible ray when its incoming
and outgoing whole decorations agree and its point misses the retained walls.
Nonvanishing and the direct-sum decomposition force the adjacent degrees to
agree. The construction retains the geometric ray, incoming tail, remaining
degree history, signs, normal velocities and final whole decoration.

In particular this supplies geometric contraction when an identity action has
no remaining active wall at its crossing. The coefficient contraction is
`homogeneousHistory_removeNth`; geometric contraction is
`AdmissibleRayRealization.removeEncounter`. Unlike artificial subdivisions,
a nonzero degree shift with unchanged spatial velocity is not deleted by this
criterion. The broken-line convention is that of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Definition 2.10
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J J' K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin (n + 1) → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {velocity : Γ → V} {f : Fin (n + 1) → V →L[ℝ] ℝ} {c : Fin (n + 1) → ℝ}
  {ε : Fin (n + 1) → SignType} {P : Fin (n + 1) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
  (i : Fin (n + 1)) (hfix : r.decoration i.castSucc = r.decoration i.succ)
  (W' : J' → Set V) (e : J' → J) (hW : ∀ j, W' j ⊆ W (e j))
  (hoff : ∀ j, r.2.ray (r.2.parameter i.succ) ∉ W' j)

include hfix in
private theorem degree_eq :
    r.1.val i = Fin.snoc (α := fun _ => Γ) r.1.val p₀ i.succ := by
  apply DirectSum.degree_eq_of_mem_mem ℳ (r.decoration_mem i) _
    (r.decoration_ne_zero i.castSucc)
  rw [hfix, decoration_def]
  exact homogeneousHistoryStage_mem_snoc ℳ T r.1.val p₀ a i.succ

/-- Omit an encounter that fixes its whole homogeneous decoration. The geometric
ray and the final coefficient are retained, and every other encounter remains
in order. In particular no shift of zero spatial direction is silently dropped. -/
def removeEncounter :
    DecoratedAdmissibleRay ℳ (i.removeNth T) p₀ a velocity (i.removeNth f)
      (i.removeNth c) (i.removeNth ε) (i.removeNth P) W' S C Q := by
  have hdir : velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ i.succ) =
      velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ i.castSucc) := by
    simpa only [Fin.snoc_castSucc] using congrArg velocity (degree_eq r i hfix).symm
  let g := r.2.removeEncounter i hdir W' e hW hoff
  have hv : i.castSucc.removeNth
      (fun j => velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ j)) =
      fun j => velocity (Fin.snoc (α := fun _ => Γ) (i.removeNth r.1.val) p₀ j) := by
    funext j
    exact congrArg velocity (congrFun (Fin.removeNth_snoc r.1.val p₀ i) j)
  have hsurv : homogeneousHistory ℳ (i.removeNth T) (i.removeNth r.1.val) a ≠ 0 := by
    rw [← homogeneousHistory_removeNth ℳ T r.1.val a i
      (by simpa only [decoration_def] using hfix)]
    exact (mem_decoratedHistorySupport ℳ T p₀ a velocity f ε _).mp r.1.property |>.1
  have hgeom : AdmissibleRayRealization (i.removeNth f) (i.removeNth c)
      (fun j => velocity (Fin.snoc (α := fun _ => Γ) (i.removeNth r.1.val) p₀ j))
      (i.removeNth P) W' S C Q :=
    g.congrVelocity hv
  refine ⟨⟨i.removeNth r.1.val, (mem_decoratedHistorySupport _ _ _ _ _ _ _ _).mpr
    ⟨hsurv, fun j => ?_⟩⟩, hgeom⟩
  have hj : velocity (Fin.snoc (α := fun _ => Γ) (i.removeNth r.1.val) p₀ j.succ) =
      velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ (i.succAbove j).succ) := by
    rw [← congrFun hv j.succ]
    exact (g.directionAt_eq j.succ).symm.trans (by
      rw [Convex.AdmissibleRayRealization.ray_removeEncounter,
        Convex.AdmissibleRayRealization.parameter_removeEncounter,
        Fin.succ_succAbove_succ, r.2.directionAt_eq])
  constructor
  · simpa only [Fin.removeNth, hj] using r.normal_velocity_eq (i.succAbove j)
  · exact r.crossing_sign (i.succAbove j)

/-- The shortened decorated ray has exactly the original degree history with
one entry deleted. -/
@[simp]
theorem history_removeEncounter :
    (r.removeEncounter i hfix W' e hW hoff).1.val = i.removeNth r.1.val := (rfl)

/-- Deleting an unchanged decoration leaves the entire geometric path intact. -/
@[simp]
theorem ray_removeEncounter : (r.removeEncounter i hfix W' e hW hoff).2.ray = r.2.ray := by
  simp only [removeEncounter, AdmissibleRayRealization.ray_congrVelocity,
    Convex.AdmissibleRayRealization.ray_removeEncounter]

/-- Every remaining encounter keeps its parameter on the original path. -/
@[simp]
theorem parameter_removeEncounter (j : Fin (n + 1)) :
    (r.removeEncounter i hfix W' e hW hoff).2.parameter j =
      r.2.parameter (i.succ.succAbove j) := by
  simp only [removeEncounter, AdmissibleRayRealization.parameter_congrVelocity,
    Convex.AdmissibleRayRealization.parameter_removeEncounter]

/-- Every retained segment keeps its whole decoration after encounter deletion. -/
@[simp]
theorem decoration_removeEncounter (j : Fin (n + 1)) :
    (r.removeEncounter i hfix W' e hW hoff).decoration j =
      r.decoration (i.castSucc.succAbove j) := by
  simp only [decoration_def, history_removeEncounter]
  exact homogeneousHistoryStage_removeNth ℳ T r.1.val a i
    (by simpa only [decoration_def] using hfix) j

/-- The final whole coefficient is preserved by geometric encounter deletion. -/
@[simp↓]
theorem decoration_zero_removeEncounter :
    (r.removeEncounter i hfix W' e hW hoff).decoration 0 = r.decoration 0 := by
  rw [decoration_zero, decoration_zero, history_removeEncounter]
  exact (homogeneousHistory_removeNth ℳ T r.1.val a i
      (by simpa only [decoration_def] using hfix)).symm

end Mei.DecoratedAdmissibleRay
