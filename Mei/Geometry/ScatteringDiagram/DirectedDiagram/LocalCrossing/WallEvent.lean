/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallEvent

/-!
# Fixed labels for signed simultaneous wall events

Extend the fixed BCH labels from
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallEvent` with an explicit
regular transverse realizability predicate, a product formula retaining all
indexed coincident walls, cutoff compatibility, and the label of each actual
admissible-segment event. The event sign is evaluated on the negative of forward
velocity, matching `AdmissibleRayRealization.wallEvents`.

The construction reuses `DirectedDiagram.wallEventLabel_eq_combinedLabel`,
`DirectedDiagram.combinedLabel_eq_prod` and
`DirectedDiagram.truncation_combinedLabel`. The crossing convention follows
Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, equation (8) and §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

local notation "W" k:max => (fun j : D.active k => DirectedWall.support (DirectedDiagram.wall D j))
local notation "f" k:max =>
  (fun j : D.active k => h.continuousRealCharacter (DirectedWall.normal (DirectedDiagram.wall D j)))

/-- A signed event has a regular point and a transverse velocity with its prescribed sign. -/
def IsRealizedEvent (k : ℕ) (e : WallEvent (D.active k)) : Prop :=
  ∃ x : {x : V // x ∉ singularSupport (W k)}, ∃ v : V,
    x.val ∈ e.support (W k) ∧
      (∀ j : D.active k, x.val ∈ (D.wall j).support → (f k) j v ≠ 0) ∧
      SignType.sign (e.normal (f k) v) = e.2

/-- Realizability is characterized by regular incidence, transversality and the event sign. -/
theorem isRealizedEvent_iff (k : ℕ) (e : WallEvent (D.active k)) :
    D.IsRealizedEvent k e ↔
      ∃ x : {x : V // x ∉ singularSupport (W k)}, ∃ v : V,
        x.val ∈ e.support (W k) ∧
          (∀ j : D.active k, x.val ∈ (D.wall j).support → (f k) j v ≠ 0) ∧
          SignType.sign (e.normal (f k) v) = e.2 := Iff.rfl

/-- An event without a regular transverse realization has identity label. -/
theorem wallEventLabel_eq_one_of_not_isRealizedEvent (k : ℕ) (e : WallEvent (D.active k))
    (he : ¬ D.IsRealizedEvent k e) : D.wallEventLabel k e = 1 := by
  apply D.wallEventLabel_eq_one_of_not_exists
  rintro ⟨x, v, hx, hreg, hs, hv⟩
  apply he
  refine ⟨⟨x, hreg⟩, v, hx, ?_, hs⟩
  intro j hj
  simpa only [h.continuousRealCharacter_apply] using
    D.realCharacter_ne_zero_of_mem_wallEvent k e hx hreg hv j hj

/-- Every enumeration of the incident indexed walls computes the fixed event
label, using the sign of forward velocity on each original coorientation. -/
theorem wallEventLabel_eq_prod (k : ℕ) (e : WallEvent (D.active k))
    {x v : V} (hx : x ∉ singularSupport (W k)) (he : x ∈ e.support (W k))
    (hv : ∀ j : D.active k, x ∈ (D.wall j).support → (f k) j v ≠ 0)
    (hs : SignType.sign (e.normal (f k) v) = e.2)
    (l : List (D.active k)) (hl : l.Nodup) (hm : ∀ j, j ∈ l ↔ j ∈ e.1.val) :
    D.wallEventLabel k e =
      (l.map fun j : D.active k => CompletedGroup.projection k (D.wall j).label ^
        (if 0 < h.realCharacter (D.wall j).normal (-v) then -1 else 1 : ℤ)).prod := by
  rw [D.wallEventLabel_eq_combinedLabel k e he hx hs
    (e.normal_ne_zero_of_mem_support (W k) (f k) he hv)]
  exact D.combinedLabel_eq_prod k x (-v) hx l hl
    (fun j => (hm j).trans ((WallEvent.mem_support e (W k) _).mp he j).symm)

/-- Lowering the cutoff removes inactive indexed factors from the event label.
The two events record the incidence and sign of the same regular transverse germ;
their chosen representative normals may differ. -/
theorem truncation_wallEventLabel {k l : ℕ} (hkl : k ≤ l)
    (e : WallEvent (D.active k)) (e' : WallEvent (D.active l)) {x v : V}
    (hk : x ∉ singularSupport (W k)) (hl : x ∉ singularSupport (W l))
    (he : x ∈ e.support (W k)) (he' : x ∈ e'.support (W l))
    (hv : ∀ j : D.active l, x ∈ (D.wall j).support → (f l) j v ≠ 0)
    (hs : SignType.sign (e.normal (f k) v) = e.2)
    (hs' : SignType.sign (e'.normal (f l) v) = e'.2) :
    (d.truncationMap ℒ hkl).bchGroupMap (D.wallEventLabel l e') =
      D.wallEventLabel k e := by
  have hvk (j : D.active k) (hj : x ∈ (D.wall j).support) : (f k) j v ≠ 0 :=
    hv ⟨j.val, D.active_mono hkl j.property⟩ hj
  rw [D.wallEventLabel_eq_combinedLabel l e' he' hl hs'
      (e'.normal_ne_zero_of_mem_support (W l) (f l) he' hv),
    D.wallEventLabel_eq_combinedLabel k e he hk hs
      (e.normal_ne_zero_of_mem_support (W k) (f k) he hvk)]
  exact D.truncation_combinedLabel hkl x (-v) hl hk

open WallComplement in
/-- The product at an actual admissible-segment event is the fixed alphabet
label whose sign is computed on the negative segment velocity. -/
theorem crossingEventProduct_eq_wallEventLabel (k : ℕ)
    {x y : WallComplement (W k)} (a : x ⟶ y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (e : WallEvent (D.active k))
    (he : AffineMap.lineMap x.val y.val t ∈ e.support (W k))
    (hs : SignType.sign (e.normal (f k) (x.val - y.val)) = e.2) :
    crossingEventProduct (fun j : D.active k => h.realCharacter (D.wall j).normal)
      (fun j => CompletedGroup.projection k (D.wall j).label)
      (D.activeLabels_commute k) a t = D.wallEventLabel k e := by
  rw [D.wallEventLabel_eq_combinedLabel k e he (a.down.regular t ht) hs
      (e.normal_ne_zero_of_mem_support (W k) (f k) he ?_),
    neg_sub, D.crossingEventProduct_eq_combinedLabel k a ht]
  intro j hj
  have hv := a.down.transverse j ⟨t, ht, hj⟩
  rw [(D.wall j).direction_support, LinearMap.mem_ker] at hv
  simpa only [← neg_sub y.val x.val, map_neg, neg_ne_zero, h.continuousRealCharacter_apply] using hv

end Mei.DirectedDiagram
