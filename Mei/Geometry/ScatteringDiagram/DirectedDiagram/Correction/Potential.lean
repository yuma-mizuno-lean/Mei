/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Boundary
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Exact

/-!
# Central potentials after outgoing joint correction

For a lower-order chamber trivialization, construct a finite family of outgoing
walls born at the next order. Subtracting their logarithmic cochain from the
crossing-defect cochain gives the coboundary of a finite polyhedral potential.
Both the correction coefficients and the potential take values in the successive
truncation kernel. Thus the potential is central, even when the retained wall
labels do not commute.

The joint meridians are chosen small enough to satisfy both
`DirectedDiagram.exists_jointObstructionCochain_eq_coboundary` and
`DirectedDiagram.exists_joint_sweep_correction_family`. Their common obstruction
is closed by square-zero. The signed sweep boundary then cancels the boundary
of the crossing defects; `PolyhedralCochain.exists_outgoing_primitive` supplies
the potential. `LieHom.kernelLogEquiv` retains the central coefficient values.
The subtraction sign reflects the convention that a positive
crossing inverts the stored wall label.

This is the cochain cancellation step in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, proof of Theorem 2.6, and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3.
The resulting potential identity is in the cochain quotient, so it includes
subdivision and cancellation of coincident contributions. Pathwise evaluation
and consistency of the combined diagram are separate conclusions.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

universe u v

namespace Mei.DirectedDiagram

variable {Γ : Type u} {V : Type v} {Λ R L ι : Type*}
  [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι} {k : ℕ}
  (σ : (D.adaptedComplex (k + 1)).walls → OrientedCell h 1)
  (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
  (cross : ∀ Q, D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
  (hk : D.LevelConsistent k)
  (b : WallComplement (fun j : D.active k => (D.wall j).support))
  (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
  (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)),
    x.val ∈ interior (P : Set V) →
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)

/-- For full initial hyperplanes and lower pure birth logarithms, construct
outgoing correction walls born exactly at order `k + 1`, together with a central
polyhedral potential for the corrected crossing-defect cochain. The finite
presentation of the potential is supplied for endpoint evaluation. No
closedness, meridian comparison or higher-order consistency is assumed. -/
theorem exists_joint_correction_potential
    (τ : (D.adaptedComplex (k + 1)).joints → OrientedCell h 2)
    (hτ : ∀ J, (τ J).carrier = (J : Set V))
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a})
    (hpure : ∀ j ∉ initial, ∃ n : Γ, d.degree n < k + 1 ∧
      ∃ a ∈ ℒ n, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ (κ : Type (max u v)) (_ : Fintype κ)
      (E : DirectedDiagram (d := d) h H κ) (η : κ → OrientedCell h 1)
      (c : κ → (d.truncationMap ℒ (Nat.le_succ k)).ker)
      (f : OrientedCell h 0 →₀ (d.truncationMap ℒ (Nat.le_succ k)).ker),
      (∀ a,
        (E.wall a).support = (η a).carrier ∧
        (∀ v : V, SignType.sign (h.realCharacter (E.wall a).normal v) =
          (η a).orientation.evalSign (fun _ : Fin 1 => v)) ∧
        (E.wall a).Outgoing ∧
        (∃ n ∈ (E.wall a).ray.rayDegrees, d.degree n = (k : ℤ) + 1 ∧
          ∃ z ∈ ℒ n, (E.wall a).label = d.expToCompletion ℒ z) ∧
        (∀ l : ℕ, a ∈ E.active l ↔ k + 1 ≤ l) ∧
        (c a : d.truncatedLie ℒ (k + 1)) =
          log (CompletedGroup.projection (k + 1) (E.wall a).label)) ∧
      PolyhedralCochain.coboundary (PolyhedralCochain.ofFinsupp (R := R) f) =
        crossingDefectCochain σ hσ cross hk b t ht -
          ∑ a, PolyhedralCochain.mk (η a) (c a) := by
  classical
  have := h.finiteDimensional
  let C := D.adaptedComplex (k + 1)
  let := Fintype.ofFinite C.joints
  have hpoint (J : C.joints) : (intrinsicInterior ℝ (J : Set V)).Nonempty := by
    have hJC := ((C.mem_cellsOfCodimension 2 J).mp J.property).1
    exact Set.Nonempty.intrinsicInterior (C.isConvexPolyhedron hJC).convex (C.nonempty J hJC)
  choose q hq using hpoint
  -- The local wall-space estimates prescribe radii before the meridians are chosen.
  obtain ⟨r, hr, hcorrection⟩ :=
    D.exists_joint_sweep_correction_family hk τ hτ q hq initial hfull hpure
  obtain ⟨s, x, p, hgeometry, hobstruction⟩ :=
    exists_jointObstructionCochain_eq_coboundary σ hσ cross hk b t ht τ hτ q hq r hr
  have hvertices (J : C.joints) (z) (hz : z ∈ (p J).vertices) :
      z.val ∈ Metric.ball (q J) (r J) := by
    have hm : z.val ∈ [(s J).points 0, (s J).points 1, (s J).points 2, (s J).points 0] := by
      rw [← (hgeometry J).2.2.1]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    have hp : z.val ∈ range (s J).points := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he | he | he
      all_goals rw [he]; exact mem_range_self _
    exact (hgeometry J).2.2.2.2.1 (subset_convexHull ℝ _ hp)
  obtain ⟨htrans, E, hE, hboundary⟩ := hcorrection x p hvertices
  let η := fun a : D.JointCorrectionIndex x p => (τ a.1).sweep (ρ a.2.val) (htrans a)
  let A := crossingDefectCochain σ hσ cross hk b t ht
  have hclosed : PolyhedralCochain.coboundary
      (D.jointObstructionCochain τ x p hτ hk) = 0 := by
    rw [hobstruction]
    exact PolyhedralCochain.coboundary_coboundary A
  have hbnd := hboundary hclosed
  -- Birth at the new order places every correction logarithm in the central kernel.
  let π := d.truncationMap ℒ (Nat.le_succ k)
  have hker (a : D.JointCorrectionIndex x p) :
      CompletedGroup.projection (k + 1) (E.wall a).label ∈ π.bchGroupMap.ker := by
    have hz : CompletedGroup.projection k (E.wall a).label = 1 := by
      by_contra hne
      have ha := (E.mem_active k a).mpr hne
      have := (hE a).2.2.2.2.2.2 k |>.mp ha
      omega
    exact (CompletedGroup.map_projection k (k + 1) (Nat.le_succ k)
      (E.wall a).label).trans hz
  let c := fun a : D.JointCorrectionIndex x p => Multiplicative.toAdd
    (π.kernelLogEquiv ⟨CompletedGroup.projection (k + 1) (E.wall a).label, hker a⟩)
  have hc (a : D.JointCorrectionIndex x p) :
      (c a : d.truncatedLie ℒ (k + 1)) =
        log (CompletedGroup.projection (k + 1) (E.wall a).label) :=
    π.coe_kernelLogEquiv _
  let B := ∑ a, PolyhedralCochain.mk (R := R) (η a) (c a)
  -- Compare in the ambient Lie algebra, then use injectivity on cochains.
  have hcancel : PolyhedralCochain.coboundary B = PolyhedralCochain.coboundary A := by
    apply PolyhedralCochain.map_injective π.ker.subtype Subtype.val_injective
    have hsource := (D.jointObstructionCochain_eq_iff τ x p hτ hk
      (PolyhedralCochain.coboundary A)).mp hobstruction
    simpa only [B, map_sum, PolyhedralCochain.map_mk, Submodule.subtype_apply, hc,
      ← PolyhedralCochain.coboundary_ofFinsupp, PolyhedralCochain.ofFinsupp_single,
      PolyhedralCochain.map_coboundary, η]
      using hbnd.trans hsource
  obtain ⟨_, f, hf, _⟩ := PolyhedralCochain.exists_outgoing_primitive (A - B) (by
    rw [map_sub, hcancel, sub_self])
  refine ⟨D.JointCorrectionIndex x p, inferInstance, E, η, c, f, ?_, hf⟩
  intro a
  obtain ⟨hs, hsign, hray, hpureE, hout, _, hactive⟩ := hE a
  refine ⟨hs, hsign, hout, ?_, hactive, hc a⟩
  obtain ⟨z, hz, hlabel⟩ := hpureE
  exact ⟨a.2.val, hray, D.degree_jointCorrectionIndex x p hk a,
    -z, (ℒ a.2.val).neg_mem hz, hlabel⟩

end Mei.DirectedDiagram
