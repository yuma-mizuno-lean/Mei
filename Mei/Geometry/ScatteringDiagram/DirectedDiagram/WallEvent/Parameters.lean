/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3.1 Pro
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.Convex.Polyhedron.Line
public import Mei.Algebra.Order.Sign
public import Mei.Geometry.Convex.Sweep.Admissible.WallEvent

/-!
# Basic data indexed by an active wall of a directed diagram

The support, real normal and offset of every directed wall are collected as
families indexed by the walls active at a given cutoff. These are the families
used by simultaneous-event encounters, keeping definitions and statements short
without hiding the underlying `DirectedWall` data. A genuine crossing of an
admissible segment by a ray then has positive event parameter, nonzero
transversality and precise incident wall set.
-/

public noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι)

/-- The support family of the walls active at cutoff `k`. -/
abbrev activeSupport (k : ℕ) : D.active k → Set V := fun c => (D.wall c).support

@[simp]
theorem activeSupport_apply (k : ℕ) (c : D.active k) :
    D.activeSupport k c = (D.wall c).support := (rfl)

/-- The real conormal family of the walls active at cutoff `k`. -/
abbrev activeNormal (k : ℕ) : D.active k → V →L[ℝ] ℝ := fun c =>
  h.continuousRealCharacter (D.wall c).normal

@[simp]
theorem activeNormal_apply (k : ℕ) (c : D.active k) :
    D.activeNormal k c = h.continuousRealCharacter (D.wall c).normal := (rfl)

/-- The real offset family of the walls active at cutoff `k`. -/
abbrev activeOffset (k : ℕ) : D.active k → ℝ := fun c => (D.wall c).offset

@[simp]
theorem activeOffset_apply (k : ℕ) (c : D.active k) :
    D.activeOffset k c = (D.wall c).offset := (rfl)

/-- A genuine crossing gives a positive ray parameter, nonzero transversality,
both signs used by the backward action, the event height, and its precise incident
wall set. The ray has arbitrary velocity `v`. -/
theorem crossing_event_data (k : ℕ)
    {x y : WallComplement (D.activeSupport k)}
    (e : x ⟶ y) (T : ℝ) (hTpos : 0 < T) {v : V}
    (hxy : x.val - y.val = T • v)
    {b : WallEvent (D.active k)} {t : ℝ} (ht : t ∈ orderedCrossingTimes e)
    (hb : b = crossingWallEvent (D.activeNormal k) e t ht) :
    0 < segmentEventParameter (D.activeNormal k) e T b ∧
      (b.normal (D.activeNormal k)) v ≠ 0 ∧
      SignType.sign ((b.normal (D.activeNormal k)) v) = b.2 ∧
      SignType.sign ((b.normal (D.activeNormal k)) (x.val - y.val)) = b.2 ∧
      (b.normal (D.activeNormal k)) (y.val +
        segmentEventParameter (D.activeNormal k) e T b • v) =
        b.offset (D.activeOffset k) ∧
      y.val + segmentEventParameter (D.activeNormal k) e T b • v ∈
        b.support (D.activeSupport k) := by
  subst b
  set c := crossingWallEvent (D.activeNormal k) e t ht with hc
  have hs := segmentEventParameter_pos (D.activeNormal k) e T hTpos ht
  have hline : AffineMap.lineMap x.val y.val t = y.val +
      segmentEventParameter (D.activeNormal k) e T
        c • v := by
    rw [lineMap_eq_add_smul (t := t) hxy, segmentEventParameter_of_mem]
  have hmem : AffineMap.lineMap x.val y.val t ∈
      (D.wall c.1.property.choose).support :=
    mem_chosenWall_crossingWallEvent (D.activeNormal k) e t ht
  have hdir := e.down.transverse
    c.1.property.choose
    ⟨t, Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e ht), hmem⟩
  rw [(D.wall c.1.property.choose).direction_support,
    LinearMap.mem_ker] at hdir
  have htrans : c.normal
      (D.activeNormal k) (y.val - x.val) ≠ 0 := by
    simpa only [D.activeNormal_apply, WallEvent.normal_def,
      h.continuousRealCharacter_apply] using hdir
  have hv : c.normal
      (D.activeNormal k) v ≠ 0 := by
    intro hz
    apply htrans
    have hyx : y.val - x.val = (-T) • v := by
      calc
        y.val - x.val = -(x.val - y.val) := by abel
        _ = -T • v := by rw [hxy]; module
    simp only [hyx, map_smul, hz, smul_zero]
  have hsign : SignType.sign (c.normal
      (D.activeNormal k) v) =
      c.2 := by
    have hn := normal_sign_crossingWallEvent (D.activeNormal k) e t ht
    calc
      SignType.sign (c.normal
        (D.activeNormal k) v) =
          SignType.sign (c.normal
            (D.activeNormal k) (x.val - y.val)) := by
        rw [hxy]
        exact (LinearMap.sign_pos_smul (c.normal (D.activeNormal k)).toLinearMap _ hTpos).symm
      _ = _ := by simpa only using hn
  have hinc : y.val + segmentEventParameter (D.activeNormal k) e T
      c • v ∈
      c.support (D.activeSupport k) := by
    rw [← hline]
    exact (WallEvent.mem_support _ _ _).2 (fun j => by
      simpa only [D.activeSupport_apply] using mem_crossingWallEvent _ e t ht j)
  have hoff := WallEvent.normal_apply_of_mem_support
    c (D.activeSupport k)
    (D.activeNormal k) (D.activeOffset k)
    (fun c z hz => by
      rw [D.activeNormal_apply, D.activeOffset_apply]
      exact (D.wall c).offset_eq hz) hinc
  exact ⟨hs, hv, hsign, (normal_sign_crossingWallEvent (D.activeNormal k) e t ht), hoff,
    hinc⟩

end Mei.DirectedDiagram
