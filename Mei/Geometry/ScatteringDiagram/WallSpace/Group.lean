/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Ray
public import Mei.Algebra.Lie.BCH.Subgroup
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Completed wall groups

A wall group consists of the completed BCH elements whose logarithm at each
finite order lies in the image of a supported-ray wall Lie algebra. These are
subgroups, and wall groups with rationally proportional normals commute
elementwise, including groups belonging to different supported rays.

Finite images commute with all truncation transitions. Membership retains the
actual allowed ray degrees through `Mei.DirectedWallSpaces.raySubmodule`.
The construction uses `LieSubalgebra.map`, `LieSubalgebra.bchSubgroup`, and
inverse images and intersections of subgroups from Mathlib.
-/

public section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L] [DecidableEq Γ]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ)

/-- The image of a supported-ray wall Lie algebra in a finite degree quotient. -/
def truncatedRayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ) (k : ℕ) :
    LieSubalgebra R (d.truncatedLie ℒ k) :=
  (H.rayLieSubalgebra w m).map (d.degreeIdeal ℒ k).mkQ

/-- A finite wall logarithm is represented by an element of the original ray sum. -/
@[simp]
theorem mem_truncatedRayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ) (k : ℕ)
    (x : d.truncatedLie ℒ k) :
    x ∈ H.truncatedRayLieSubalgebra w m k ↔
      ∃ y ∈ H.raySubmodule w m, (d.degreeIdeal ℒ k).mkQ y = x := by
  simp only [truncatedRayLieSubalgebra, LieSubalgebra.mem_map, mem_rayLieSubalgebra]

/-- Truncation maps a finer ray Lie algebra onto the corresponding coarser one. -/
theorem map_truncatedRayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ)
    {k l : ℕ} (h : k ≤ l) :
    (H.truncatedRayLieSubalgebra w m l).map (d.truncationMap ℒ h) =
      H.truncatedRayLieSubalgebra w m k := by
  ext x
  simp only [LieSubalgebra.mem_map, mem_truncatedRayLieSubalgebra]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by simp [LieIdeal.mkQ_apply]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(d.degreeIdeal ℒ l).mkQ z, ⟨z, hz, rfl⟩, by simp [LieIdeal.mkQ_apply]⟩

/-- A ray not meeting the cutoff has its entire wall sum in the degree ideal. -/
theorem raySubmodule_le_degreeIdeal (w : SupportedRay d) (m : Λ →+ ℤ) (k : ℕ)
    (hw : w ∉ d.raysAtOrder k) : H.raySubmodule w m ≤ (d.degreeIdeal ℒ k).toSubmodule := by
  rw [raySubmodule_def]
  refine iSup_le fun n => (H.wall_le_piece n m).trans (d.le_degreeIdeal ℒ ?_)
  by_contra hn
  exact hw ((d.mem_raysAtOrder).mpr ⟨n, n.property, le_of_not_gt hn⟩)

/-- Rays with no actual allowed degree at or below the cutoff have zero finite image. -/
theorem truncatedRayLieSubalgebra_eq_bot (w : SupportedRay d) (m : Λ →+ ℤ) (k : ℕ)
    (hw : w ∉ d.raysAtOrder k) : H.truncatedRayLieSubalgebra w m k = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (H.mem_truncatedRayLieSubalgebra w m k x).mp hx
  exact (d.degreeIdeal ℒ k).mkQ_eq_zero.mpr (H.raySubmodule_le_degreeIdeal w m k hw hy)

/-- Proportional normals still give zero brackets after finite truncation. -/
theorem lie_eq_zero_of_mem_truncatedRayLieSubalgebra {w v : SupportedRay d}
    {m m' : Λ →+ ℤ} {k : ℕ} {x y : d.truncatedLie ℒ k}
    (hx : x ∈ H.truncatedRayLieSubalgebra w m k)
    (hy : y ∈ H.truncatedRayLieSubalgebra v m' k)
    {c e : ℤ} (hc : c ≠ 0) (he : e ≠ 0) (hm : c • m = e • m') : ⁅x, y⁆ = 0 := by
  obtain ⟨a, ha, hax⟩ := (H.mem_truncatedRayLieSubalgebra w m k _).mp hx
  obtain ⟨b, hb, hby⟩ := (H.mem_truncatedRayLieSubalgebra v m' k _).mp hy
  rw [← hax, ← hby, ← LieHom.map_lie,
    H.lie_eq_zero_of_mem_raySubmodule ha hb hc he hm, map_zero]

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- The completed subgroup whose finite logarithms lie in the supported-ray
wall spaces. The primitive generator need not itself be an allowed degree. -/
noncomputable def wallGroup (w : SupportedRay d) (m : Λ →+ ℤ) :
    Subgroup (d.completedBCHGroup ℒ) :=
  ⨅ k, (H.truncatedRayLieSubalgebra w m k).bchSubgroup.comap
    (CompletedGroup.projection k)

/-- A completed wall label is tested by its logarithms at all finite orders. -/
@[simp]
theorem mem_wallGroup (w : SupportedRay d) (m : Λ →+ ℤ) (g : d.completedBCHGroup ℒ) :
    g ∈ H.wallGroup w m ↔ ∀ k,
      BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) ∈
        H.truncatedRayLieSubalgebra w m k := by
  simp only [wallGroup, Subgroup.mem_iInf]
  exact forall_congr' fun k => LieSubalgebra.mem_bchSubgroup _ _

/-- Exponentiating an element of a supported-ray wall algebra gives a completed wall label. -/
theorem expToCompletion_mem_wallGroup {w : SupportedRay d} {m : Λ →+ ℤ} {x : L}
    (hx : x ∈ H.raySubmodule w m) : d.expToCompletion ℒ x ∈ H.wallGroup w m := by
  rw [mem_wallGroup]
  intro k
  rw [PositiveDegrees.projection_expToCompletion, BCHGroup.log_exp,
    mem_truncatedRayLieSubalgebra]
  exact ⟨x, hx, rfl⟩

/-- A finite wall logarithm has no homogeneous component off its actual supported ray.
The primitive generator need not itself belong to the positive monoid. -/
theorem decompose_log_projection_eq_zero_of_notMem_rayDegrees
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) (k : ℕ) {n : Γ} (hn : n ∉ w.rayDegrees) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (BCHGroup.log (CompletedGroup.projection k g)) n : d.truncatedLie ℒ k) = 0 := by
  obtain ⟨y, hy, he⟩ := (H.mem_truncatedRayLieSubalgebra w m k _).mp
    ((H.mem_wallGroup w m g).mp hg k)
  rw [← he, LieIdeal.mkQ_apply, d.decompose_truncatedGrading_mk,
    H.decompose_eq_zero_of_notMem_rayDegrees hy hn]
  exact Submodule.Quotient.mk_zero _

/-- A completed wall label is invisible below the first actual degree on its ray. -/
theorem projection_eq_one_of_notMem_raysAtOrder {w : SupportedRay d} {m : Λ →+ ℤ}
    {g : d.completedBCHGroup ℒ} (hg : g ∈ H.wallGroup w m) (k : ℕ)
    (hw : w ∉ d.raysAtOrder k) : CompletedGroup.projection k g = 1 := by
  apply BCHGroup.log_injective (L := d.truncatedLie ℒ k)
  have h := (H.mem_wallGroup w m g).mp hg k
  rw [H.truncatedRayLieSubalgebra_eq_bot w m k hw, LieSubalgebra.mem_bot] at h
  exact h.trans BCHGroup.log_one.symm

/-- Only the identity completed label has zero normal. -/
@[simp]
theorem wallGroup_zero (w : SupportedRay d) : H.wallGroup w 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  apply CompletedGroup.ext
  intro k
  rw [map_one]
  apply BCHGroup.log_injective (L := d.truncatedLie ℒ k)
  obtain ⟨y, hy, heq⟩ := (H.mem_truncatedRayLieSubalgebra w 0 k _).mp
    ((H.mem_wallGroup w 0 g).mp hg k)
  rw [H.raySubmodule_zero, Submodule.mem_bot] at hy
  subst y
  exact ((map_zero (d.degreeIdeal ℒ k).mkQ).symm.trans heq).symm.trans
    (BCHGroup.log_one (L := d.truncatedLie ℒ k)).symm

/-- Nonzero integer rescaling of the normal preserves the completed wall group. -/
@[simp]
theorem wallGroup_rescale (w : SupportedRay d) (m : Λ →+ ℤ)
    (c : ℤ) (hc : c ≠ 0) : H.wallGroup w (c • m) = H.wallGroup w m := by
  ext g
  simp only [mem_wallGroup, mem_truncatedRayLieSubalgebra, H.raySubmodule_rescale w m c hc]

/-- Completed labels with proportional normals commute, with no restriction on
their supported rays or the geometric images of those rays. -/
theorem commute_of_mem_wallGroup {w v : SupportedRay d} {m m' : Λ →+ ℤ}
    {g h : d.completedBCHGroup ℒ} (hg : g ∈ H.wallGroup w m) (hh : h ∈ H.wallGroup v m')
    {c e : ℤ} (hc : c ≠ 0) (he : e ≠ 0) (hm : c • m = e • m') : Commute g h := by
  apply CompletedGroup.ext
  intro k
  rw [map_mul, map_mul]
  have hlie := H.lie_eq_zero_of_mem_truncatedRayLieSubalgebra
    ((H.mem_wallGroup w m g).mp hg k) ((H.mem_wallGroup v m' h).mp hh k) hc he hm
  have hc := BCHGroup.commute_exp_of_lie_eq_zero _ _ hlie
  rw [BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g),
    BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k h)] at hc
  exact hc.eq

/-- Every completed wall group is abelian. -/
noncomputable instance wallGroup_isMulCommutative (w : SupportedRay d) (m : Λ →+ ℤ) :
    IsMulCommutative (H.wallGroup w m) :=
  IsMulCommutative.of_setLike_mul_comm fun _ hg _ hh =>
    (H.commute_of_mem_wallGroup hg hh one_ne_zero one_ne_zero rfl).eq

end Mei.DirectedWallSpaces
