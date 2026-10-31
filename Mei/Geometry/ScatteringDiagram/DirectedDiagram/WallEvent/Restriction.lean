/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.WallEvent.Restriction
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallEvent

/-!
# Restricting event labels to a lower cutoff

Lowering the cutoff retains only the active indexed walls. Restricting a
regular transverse event to those indices constructs its lower-order event,
whose chosen normal can differ in coorientation from the original one. Its
fixed propagation label is the truncation of the original label. If no incident
wall remains, that truncation is the identity.

This combines `WallEvent.restrict` with `truncation_combinedLabel` and
`wallEventLabel_eq_combinedLabel`. In particular no independent choice of a
lower-order event or regularity witness is required. Indexed coincident walls
remain separate, even when their combined label cancels. The sign and forward
propagation conventions follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, equation (8) and Definition 2.10
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

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

/-- Project a realized signed event by restricting its incident indices to the
lower active alphabet. A surviving event receives its new normal-velocity sign;
an event with no retained incident wall has identity projected label. This
requires no consistency, finiteness of the original wall index type, or
noncancellation hypothesis on event labels. -/
theorem truncation_wallEventLabel_restrict {k l : ℕ} (hkl : k ≤ l)
    (e : WallEvent (D.active l)) {x v : V}
    (hx : x ∈ e.support (W l)) (hreg : x ∉ singularSupport (W l))
    (hs : SignType.sign (e.normal (f l) v) = e.2)
    (hv : e.normal (f l) v ≠ 0) :
    let u : D.active k ↪ D.active l :=
      ⟨Set.inclusion (D.active_mono hkl), Set.inclusion_injective _⟩
    (d.truncationMap ℒ hkl).bchGroupMap (D.wallEventLabel l e) =
      (e.restrict u (f k) v).elim 1 (D.wallEventLabel k) := by
  dsimp only
  let u : D.active k ↪ D.active l :=
    ⟨Set.inclusion (D.active_mono hkl), Set.inclusion_injective _⟩
  have hk : x ∉ singularSupport (W k) :=
    fun h' => hreg (singularSupport_comp_subset (W l) u h')
  have htrans (j : D.active l) (hj : x ∈ (D.wall j).support) :
      (f l) j v ≠ 0 := by
    simpa only [h.continuousRealCharacter_apply] using
      D.realCharacter_ne_zero_of_mem_wallEvent l e hx hreg hv j hj
  cases he : e.restrict u (f k) v with
  | none =>
    rw [D.wallEventLabel_eq_combinedLabel l e hx hreg hs hv,
      D.truncation_combinedLabel hkl x (-v) hreg hk]
    exact D.combinedLabel_eq_one_of_forall_notMem k x (-v) hk (fun j hj =>
      WallEvent.notMem_iUnion_of_restrict_eq_none he (W l) hx (mem_iUnion.mpr ⟨j, hj⟩))
  | some b =>
    have hb := WallEvent.support_subset_of_restrict_eq_some he (W l) hx
    exact D.truncation_wallEventLabel hkl b e hk hreg hb hx htrans
      ((WallEvent.restrict_eq_some_iff ..).mp he).2 hs

end Mei.DirectedDiagram
