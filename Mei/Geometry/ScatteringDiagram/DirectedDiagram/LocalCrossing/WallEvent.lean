/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing.Constancy
public import Mei.Geometry.Convex.Polyhedron.WallEvent
public import Mei.Geometry.Toric.Algebraic.DualLattice

/-!
# Fixed labels for signed simultaneous wall events

At a fixed cutoff, assign a BCH label to each signed event of the active indexed
wall family. The sign is evaluated on the negative of forward velocity, as in
`AdmissibleRayRealization.wallEvents`. Every regular transverse realization of
an event computes this same label. Thus homogeneous coefficient histories can
use a fixed finite alphabet, independently of encounter positions and velocities.
Unrealizable events, including sign-zero events, receive the identity label.

Reversing the sign inverts the event label. The labels compute both the
individual events of admissible segments and arbitrarily short transverse path
products. Coincident walls retain all their indexed factors, including opposite
coorientations; no consistency assumption is imposed.

The construction uses `WallEvent`,
`DirectedDiagram.combinedLabel_eq_of_incident_iff_of_mul_pos` and the existing
short-segment realization of combined labels. The crossing convention follows
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

private theorem wallEvent_realization_neg (k : ℕ) (e : WallEvent (D.active k))
    {x v : V} (he : x ∈ e.support (W k))
    (hv : ∀ j : D.active k, x ∈ (D.wall j).support → (f k) j v ≠ 0)
    (hs : SignType.sign (e.normal (f k) v) = e.2) :
    x ∈ WallEvent.support (e.1, -e.2) (W k) ∧
      (∀ j : D.active k, x ∈ (D.wall j).support → (f k) j (-v) ≠ 0) ∧
      SignType.sign (WallEvent.normal (e.1, -e.2) (f k) (-v)) = -e.2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [WallEvent.mem_support] using he
  · intro j hj
    simpa only [map_neg, neg_ne_zero] using hv j hj
  · simpa only [WallEvent.normal_def, map_neg, Left.sign_neg] using congrArg Neg.neg hs

/-- The fixed signed label of a simultaneous event. Its sign uses the negative
of forward velocity. Events with no regular transverse realization have label one. -/
def wallEventLabel (k : ℕ) (e : WallEvent (D.active k)) : d.truncatedGroup ℒ k := by
  classical
  exact if he : D.IsRealizedEvent k e then
    D.combinedLabel k he.choose.val (-he.choose_spec.choose) he.choose.property
  else 1

/-- The fixed event label agrees with every regular transverse realization,
with forward velocity `-v`. No position or velocity choices remain in the label. -/
theorem wallEventLabel_eq_combinedLabel (k : ℕ) (e : WallEvent (D.active k))
    {x v : V} (hx : x ∉ singularSupport (W k)) (he : x ∈ e.support (W k))
    (hv : ∀ j : D.active k, x ∈ (D.wall j).support → (f k) j v ≠ 0)
    (hs : SignType.sign (e.normal (f k) v) = e.2) :
    D.wallEventLabel k e = D.combinedLabel k x (-v) hx := by
  classical
  unfold wallEventLabel
  split_ifs with hr
  · obtain ⟨hpoint, _, hsign⟩ := hr.choose_spec.choose_spec
    apply D.combinedLabel_eq_of_incident_iff_of_mul_pos
      hr.choose.property hx (fun j => ((WallEvent.mem_support e (W k) _).mp hpoint j).trans
        ((WallEvent.mem_support e (W k) _).mp he j).symm)
      e.1.property.choose (e.support_subset (W k) e.1.property.choose_spec hpoint)
    have hne := e.normal_ne_zero_of_mem_support (W k) (f k) he hv
    have heq : SignType.sign (e.normal (f k) hr.choose_spec.choose) =
        SignType.sign (e.normal (f k) v) := hsign.trans hs.symm
    have hpos : 0 < e.normal (f k) hr.choose_spec.choose * e.normal (f k) v := by
      apply sign_eq_one_iff.mp
      rw [sign_mul, heq, ← sign_mul]
      exact sign_pos (mul_self_pos.mpr hne)
    simpa only [map_neg, neg_mul_neg, WallEvent.normal_def,
      h.continuousRealCharacter_apply] using hpos
  · exact False.elim (hr ⟨⟨x, hx⟩, v, he, hv, hs⟩)

/-- An event admitting no regular transverse realization has identity label,
including incidence sets that never occur away from singular support. -/
theorem wallEventLabel_eq_one_of_not_exists (k : ℕ) (e : WallEvent (D.active k))
    (he : ¬ D.IsRealizedEvent k e) :
    D.wallEventLabel k e = 1 := by
  classical
  simp only [wallEventLabel, dite_eq_right he]

/-- Sign-zero events cannot occur transversely and have identity label. -/
@[simp]
theorem wallEventLabel_zero (k : ℕ) (s : {s : Finset (D.active k) // s.Nonempty}) :
    D.wallEventLabel k (s, 0) = 1 := by
  apply D.wallEventLabel_eq_one_of_not_exists
  rintro ⟨x, v, he, hv, hs⟩
  exact WallEvent.normal_ne_zero_of_mem_support (s, 0) (W k) (f k) he hv
    (sign_eq_zero_iff.mp hs)

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
  rw [D.wallEventLabel_eq_combinedLabel k e hx he hv hs]
  exact D.combinedLabel_eq_prod k x (-v) hx l hl
    (fun j => (hm j).trans ((WallEvent.mem_support e (W k) _).mp he j).symm)

/-- Reversing a realized event's sign inverts its entire simultaneous label,
including every coincident indexed wall. -/
private theorem wallEventLabel_neg_of_mem_support (k : ℕ) (e : WallEvent (D.active k))
    {x v : V} (hx : x ∉ singularSupport (W k)) (he : x ∈ e.support (W k))
    (hv : ∀ j : D.active k, x ∈ (D.wall j).support → (f k) j v ≠ 0)
    (hs : SignType.sign (e.normal (f k) v) = e.2) :
    D.wallEventLabel k (e.1, -e.2) = (D.wallEventLabel k e)⁻¹ := by
  obtain ⟨he', hv', hs'⟩ := D.wallEvent_realization_neg k e he hv hs
  rw [D.wallEventLabel_eq_combinedLabel k (e.1, -e.2) hx he' hv' hs', neg_neg,
    D.wallEventLabel_eq_combinedLabel k e hx he hv hs,
    D.combinedLabel_neg k x v hx
      (fun j hj => by simpa only [h.continuousRealCharacter_apply] using hv j hj), inv_inv]

/-- Reversing the sign inverts the fixed label. This includes unrealizable and
sign-zero events, whose labels are the identity. -/
@[simp]
theorem wallEventLabel_neg (k : ℕ) (e : WallEvent (D.active k)) :
    D.wallEventLabel k (e.1, -e.2) = (D.wallEventLabel k e)⁻¹ := by
  classical
  by_cases hr : D.IsRealizedEvent k e
  · obtain ⟨x, v, he, hv, hs⟩ := hr
    exact D.wallEventLabel_neg_of_mem_support k e x.property he hv hs
  · rw [D.wallEventLabel_eq_one_of_not_exists k e hr, inv_one]
    apply D.wallEventLabel_eq_one_of_not_exists
    rintro ⟨x, v, he, hv, hs⟩
    apply hr
    have hr' : D.IsRealizedEvent k (e.1, -(-e.2)) :=
      ⟨x, -v, D.wallEvent_realization_neg k (e.1, -e.2) he hv hs⟩
    simpa only [neg_neg] using hr'

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
  rw [D.wallEventLabel_eq_combinedLabel l e' hl he' hv hs',
    D.wallEventLabel_eq_combinedLabel k e hk he hvk hs]
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
  rw [D.wallEventLabel_eq_combinedLabel k e (a.down.regular t ht) he ?_ hs,
    neg_sub, D.crossingEventProduct_eq_combinedLabel k a ht]
  intro j hj
  have hv := a.down.transverse j ⟨t, ht, hj⟩
  rw [(D.wall j).direction_support, LinearMap.mem_ker] at hv
  simpa only [← neg_sub y.val x.val, map_neg, neg_ne_zero, h.continuousRealCharacter_apply] using hv

/-- Every regular transverse realization of an event has arbitrarily short
admissible paths computing its fixed label, oriented in forward velocity `-v`. -/
theorem eventually_exists_levelPathProduct_eq_wallEventLabel (k : ℕ)
    (e : WallEvent (D.active k)) {x v : V}
    (hx : x ∉ singularSupport (W k)) (he : x ∈ e.support (W k))
    (hv : ∀ j : D.active k, x ∈ (D.wall j).support → (f k) j v ≠ 0)
    (hs : SignType.sign (e.normal (f k) v) = e.2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      ∃ (z w : WallComplement (W k)) (a : z ⟶ w),
        z.val = x + b • v ∧ w.val = x - b • v ∧
        D.levelPathProduct k a.toPath = D.wallEventLabel k e := by
  rw [D.wallEventLabel_eq_combinedLabel k e hx he hv hs]
  simpa only [smul_neg, sub_eq_add_neg, neg_neg] using
    D.eventually_exists_levelPathProduct_eq_combinedLabel k x (-v) hx
      (fun j hj => by
        simpa only [map_neg, neg_ne_zero, h.continuousRealCharacter_apply] using hv j hj)

end Mei.DirectedDiagram
