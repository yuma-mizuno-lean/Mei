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

A signed event in the active wall alphabet determines a single BCH label,
independent of its regular encounter point and transverse direction. Its sign
is evaluated on the negative of forward velocity, as in admissible backward
rays; its label acts in the forward direction. Events with no regular transverse
realization have label one and cannot occur at a regular transverse encounter.
Reversing the sign inverts the whole label. Actual isolating segments compute
this label, and arbitrarily short such segments exist at every regular
transverse event. An explicit realizability predicate records these encounters.
The label has an indexed product formula, agrees with actual segment event
products, and is compatible with lowering the cutoff.

The construction uses `DirectedDiagram.combinedLabel` and its constancy on
regular incidence strata, together with `DirectedDiagram.combinedLabel_eq_prod`
and `DirectedDiagram.truncation_combinedLabel`. Every indexed coincident wall contributes
its signed factor. The crossing convention follows Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, equation (8) and §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

local notation "W" k => fun j : D.active k => DirectedWall.support (DirectedDiagram.wall D j)
local notation "f" k => fun j : D.active k => h.continuousRealCharacter
  (DirectedWall.normal (DirectedDiagram.wall D j))

open Classical in
/-- The fixed forward propagation label of a signed simultaneous event.
The event sign uses the negative of forward velocity. An event without a regular
transverse realization is assigned the identity. -/
def wallEventLabel (k : ℕ) (e : WallEvent (D.active k)) : d.truncatedGroup ℒ k :=
  if hex : ∃ x v, x ∈ e.support (W k) ∧ x ∉ singularSupport (W k) ∧
      SignType.sign (e.normal (f k) v) = e.2 ∧ e.normal (f k) v ≠ 0 then
    D.combinedLabel k hex.choose (-hex.choose_spec.choose)
      hex.choose_spec.choose_spec.2.1
  else 1

/-- Any regular transverse realization computes the same fixed event label.
The vector `v` is the negative of forward velocity. -/
theorem wallEventLabel_eq_combinedLabel (k : ℕ) (e : WallEvent (D.active k))
    {x v : V} (hx : x ∈ e.support (W k)) (hreg : x ∉ singularSupport (W k))
    (hs : SignType.sign (e.normal (f k) v) = e.2) (hv : e.normal (f k) v ≠ 0) :
    D.wallEventLabel k e = D.combinedLabel k x (-v) hreg := by
  classical
  have hex : ∃ x v, x ∈ e.support (W k) ∧ x ∉ singularSupport (W k) ∧
      SignType.sign (e.normal (f k) v) = e.2 ∧ e.normal (f k) v ≠ 0 :=
    ⟨x, v, hx, hreg, hs, hv⟩
  rw [wallEventLabel, dite_eq_left hex]
  obtain ⟨hx₀, hreg₀, hs₀, hv₀⟩ := hex.choose_spec.choose_spec
  have hpos : 0 < e.normal (f k) hex.choose_spec.choose * e.normal (f k) v := by
    have heq := hs₀.trans hs.symm
    rcases lt_or_gt_of_ne hv₀ with hn | hp
    · exact mul_pos_of_neg_of_neg hn
        (sign_eq_neg_one_iff.mp (heq.symm.trans (sign_eq_neg_one_iff.mpr hn)))
    · exact mul_pos hp
        (sign_eq_one_iff.mp (heq.symm.trans (sign_eq_one_iff.mpr hp)))
  apply D.combinedLabel_eq_of_incident_iff_of_mul_pos hreg₀ hreg
    (fun j => ((e.mem_support _ _).mp hx₀ j).trans ((e.mem_support _ _).mp hx j).symm)
    e.1.property.choose
    (e.support_subset (W k) e.1.property.choose_spec hx₀)
  simpa only [map_neg, neg_mul_neg, WallEvent.normal_def,
    TauCeti.Toric.IsIntegralLattice.continuousRealCharacter_apply] using hpos

/-- The default value is the identity when the construction has no
regular transverse witness. Realized events can also have identity label
when their factors cancel. -/
theorem wallEventLabel_eq_one_of_not_exists (k : ℕ) (e : WallEvent (D.active k))
    (he : ¬ ∃ x v, x ∈ e.support (W k) ∧ x ∉ singularSupport (W k) ∧
      SignType.sign (e.normal (f k) v) = e.2 ∧ e.normal (f k) v ≠ 0) :
    D.wallEventLabel k e = 1 := by
  classical
  rw [wallEventLabel, dite_eq_right he]

/-- A zero-sign event is never transverse and receives the identity label. -/
@[simp]
theorem wallEventLabel_eq_one_of_sign_eq_zero (k : ℕ) (e : WallEvent (D.active k))
    (he : e.2 = 0) : D.wallEventLabel k e = 1 := by
  apply D.wallEventLabel_eq_one_of_not_exists
  rintro ⟨x, v, _, _, hs, hv⟩
  exact hv (sign_eq_zero_iff.mp (hs.trans he))

/-- At a regular event, transversality to its chosen normal implies
transversality to every incident indexed wall, including opposite coorientations. -/
theorem realCharacter_ne_zero_of_mem_wallEvent (k : ℕ) (e : WallEvent (D.active k))
    {x v : V} (hx : x ∈ e.support (W k)) (hreg : x ∉ singularSupport (W k))
    (hv : e.normal (f k) v ≠ 0) (j : D.active k) (hj : x ∈ (D.wall j).support) :
    h.realCharacter (D.wall j).normal v ≠ 0 := by
  have hdir := congrArg AffineSubspace.direction
    (affineSpan_eq_of_notMem_singularSupport hreg
      (e.support_subset (W k) e.1.property.choose_spec hx) hj)
  intro hz
  apply hv
  have hm : v ∈ (affineSpan ℝ (D.wall j).support).direction := by
    rw [(D.wall j).direction_support, LinearMap.mem_ker]
    exact hz
  rw [← hdir, (D.wall e.1.property.choose).direction_support, LinearMap.mem_ker] at hm
  simpa only [WallEvent.normal_def, h.continuousRealCharacter_apply] using hm

/-- Reversing the event sign inverts the entire combined label. The law also
holds for unrealizable events, which have identity labels on both sides. -/
@[simp]
theorem wallEventLabel_neg (k : ℕ) (e : WallEvent (D.active k)) :
    D.wallEventLabel k (e.1, -e.2) = (D.wallEventLabel k e)⁻¹ := by
  classical
  by_cases hex : ∃ x v, x ∈ e.support (W k) ∧ x ∉ singularSupport (W k) ∧
      SignType.sign (e.normal (f k) v) = e.2 ∧ e.normal (f k) v ≠ 0
  · obtain ⟨x, v, hx, hreg, hs, hv⟩ := hex
    have hx' : x ∈ WallEvent.support (e.1, -e.2) (W k) := by
      simpa only [WallEvent.mem_support] using hx
    have hs' : SignType.sign
        (WallEvent.normal (e.1, -e.2) (f k) (-v)) = -e.2 := by
      simpa only [WallEvent.normal_def, map_neg, Left.sign_neg] using congrArg Neg.neg hs
    have hv' : WallEvent.normal (e.1, -e.2) (f k) (-v) ≠ 0 := by
      simpa only [WallEvent.normal_def, map_neg, neg_ne_zero] using hv
    rw [D.wallEventLabel_eq_combinedLabel k _ hx' hreg hs' hv',
      D.wallEventLabel_eq_combinedLabel k e hx hreg hs hv, neg_neg,
      D.combinedLabel_neg k x v hreg
        (D.realCharacter_ne_zero_of_mem_wallEvent k e hx hreg hv), inv_inv]
  · rw [D.wallEventLabel_eq_one_of_not_exists k e hex, inv_one]
    apply D.wallEventLabel_eq_one_of_not_exists
    rintro ⟨x, v, hx, hreg, hs, hv⟩
    apply hex
    refine ⟨x, -v, ?_, hreg, ?_, ?_⟩
    · simpa only [WallEvent.mem_support] using hx
    · simpa only [WallEvent.normal_def, map_neg, Left.sign_neg, neg_neg]
        using congrArg Neg.neg hs
    · simpa only [WallEvent.normal_def, map_neg, neg_ne_zero] using hv

/-- An actual segment isolating a signed event computes its fixed forward label.
The event sign is measured on the backward displacement `x - y`. -/
theorem levelPathProduct_toPath_eq_wallEventLabel (k : ℕ) (b : WallEvent (D.active k))
    {x y : WallComplement (W k)} (a : x ⟶ y) {θ : V}
    (hθ : θ ∈ b.support (W k)) (hreg : θ ∉ singularSupport (W k))
    (hs : SignType.sign (b.normal (f k) (x.val - y.val)) = b.2)
    (hv : b.normal (f k) (x.val - y.val) ≠ 0) (t : ℝ)
    (hcross : ∀ j s, (j, s) ∈ crossings x y ↔ θ ∈ (D.wall j).support ∧ s = t) :
    D.levelPathProduct k a.toPath = D.wallEventLabel k b := by
  rw [D.levelPathProduct_toPath_eq_combinedLabel k a θ hreg t hcross,
    D.wallEventLabel_eq_combinedLabel k b hθ hreg hs hv, neg_sub]

/-- Every regular transverse event is realized by arbitrarily short admissible
segments carrying its fixed forward label. Positive radii all sufficiently close
to zero work; the first endpoint is on the incoming side of the event. -/
theorem eventually_exists_levelPathProduct_eq_wallEventLabel (k : ℕ)
    (e : WallEvent (D.active k)) {θ v : V} (hθ : θ ∈ e.support (W k))
    (hreg : θ ∉ singularSupport (W k))
    (hs : SignType.sign (e.normal (f k) v) = e.2) (hv : e.normal (f k) v ≠ 0) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (W k)) (b : x ⟶ y),
        x.val = θ + a • v ∧ y.val = θ - a • v ∧
        D.levelPathProduct k b.toPath = D.wallEventLabel k e := by
  have htrans := D.realCharacter_ne_zero_of_mem_wallEvent k e hθ hreg hv
  filter_upwards [D.eventually_exists_levelPathProduct_eq_combinedLabel k θ (-v) hreg
    (fun j hj => by simpa only [map_neg, neg_ne_zero] using htrans j hj)] with a ha
  obtain ⟨x, y, b, hx, hy, hb⟩ := ha
  refine ⟨x, y, b, ?_, ?_, ?_⟩
  · simpa only [smul_neg, sub_neg_eq_add] using hx
  · simpa only [smul_neg, sub_eq_add_neg] using hy
  · exact hb.trans (D.wallEventLabel_eq_combinedLabel k e hθ hreg hs hv).symm

/-- An event without a regular transverse realization has identity label. -/
theorem wallEventLabel_eq_one_of_not_isRealizedEvent (k : ℕ) (e : WallEvent (D.active k))
    (he : ¬ e.IsRealizedEvent (W k) (f k)) : D.wallEventLabel k e = 1 := by
  apply D.wallEventLabel_eq_one_of_not_exists
  rintro ⟨x, v, hx, hreg, hs, hv⟩
  apply he
  rw [WallEvent.isRealizedEvent_iff]
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
