/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Chamber transports and their lifts

Endpoint transport of a consistent finite-order directed diagram is locally constant
on the complement of its active walls. It therefore descends to the actual connected
chambers, without choosing a polyhedral subdivision or a representative point in each
chamber. Surjectivity of the BCH truncations lifts these chamber values to any higher
order, with the base chamber normalized to the identity. For every higher-order path,
the crossing product gauged by these lifts lies in the truncation kernel. For successive
orders this is the central kernel used for additive transport defects.

The construction uses `DirectedDiagram.levelTransport`, Mathlib's
`Continuous.connectedComponentsLift`, and the surjectivity of the existing Lie
truncations. Local constancy follows from identity transport on wall-free segments.
The walls may overlap, have lineality, and vary with the cutoff; consistency is required
only at the lower order, not at the order to which the transports are lifted.
-/

public section

noncomputable section

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

/-- The actual connected chambers of the finite active-wall complement. The subtype
uses the topology induced from the ambient vector space. -/
abbrev LevelChamber (k : ℕ) :=
  ConnectedComponents {x : V // ∀ j : D.active k, x ∉ (D.wall j).support}

/-- The chamber containing a finite-order allowed endpoint. -/
def levelChamber {k : ℕ}
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) : D.LevelChamber k :=
  ConnectedComponents.mk ⟨x.val, x.notMem⟩

/-- Two endpoints determine the same chamber exactly when their points lie in the
same connected component of the active-wall complement. -/
theorem levelChamber_eq_iff {k : ℕ}
    (x y : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.levelChamber x = D.levelChamber y ↔
      (⟨x.val, x.notMem⟩ : {z : V // ∀ j : D.active k, z ∉ (D.wall j).support}) ∈
        connectedComponent ⟨y.val, y.notMem⟩ := by
  exact ConnectedComponents.coe_eq_coe'

/-- Every actual chamber contains an allowed endpoint. -/
theorem levelChamber_surjective (k : ℕ) :
    Function.Surjective (D.levelChamber (k := k)) := by
  intro C
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  exact ⟨⟨x.val, x.property⟩, rfl⟩

/-- Consistent endpoint transport is locally constant on the active-wall complement. -/
theorem isLocallyConstant_levelTransport {k : ℕ} (hD : D.LevelConsistent k)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    IsLocallyConstant (fun y : {y : V // ∀ j : D.active k, y ∉ (D.wall j).support} =>
      D.levelTransport k hD x ⟨y.val, y.property⟩) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro y
  have hopen : IsOpen {z : V | ∀ j : D.active k, z ∉ (D.wall j).support} := by
    simpa only [ofPred_forall, compl_def] using
      isOpen_iInter_of_finite
        (fun j : D.active k => (D.wall j).isConvexPolyhedron.isClosed.isOpen_compl)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen y.val y.property
  refine ⟨Subtype.val ⁻¹' Metric.ball y.val r,
    Metric.isOpen_ball.preimage continuous_subtype_val, by simpa, ?_⟩
  intro z hz
  let a : WallComplement (fun j : D.active k => (D.wall j).support) := ⟨y.val, y.property⟩
  let b : WallComplement (fun j : D.active k => (D.wall j).support) := ⟨z.val, z.property⟩
  have he : WallComplement.crossings a b = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨j, t⟩ hm
    obtain ⟨ht, hj⟩ := (WallComplement.mem_crossings a b j t).mp hm
    exact hball ((convex_ball y.val r).lineMap_mem (by simpa [a] using hr) hz ht) j hj
  let e : a ⟶ b := ⟨WallComplement.AdmissibleSegment.of_crossings_eq_empty
    (fun j => (D.wall j).isConvexPolyhedron.isClosed) he⟩
  have hprod := D.levelPathProduct_eq_one_of_crossings_eq_empty k e he
  have hab : D.levelTransport k hD a b = 1 :=
    (D.levelTransport_eq_levelPathProduct hD e.toPath).trans hprod
  simpa only [hab, one_mul] using D.levelTransport_comp hD x a b

/-- Transport from a basepoint to a connected chamber, independent of its point. -/
def chamberTransport {k : ℕ} (hD : D.LevelConsistent k)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.LevelChamber k → d.truncatedGroup ℒ k := by
  letI : TopologicalSpace (d.truncatedGroup ℒ k) := ⊥
  letI := discreteTopology_bot (d.truncatedGroup ℒ k)
  exact (D.isLocallyConstant_levelTransport hD x).continuous.connectedComponentsLift

/-- At the chamber of an allowed point, chamber transport is endpoint transport. -/
@[simp]
theorem chamberTransport_levelChamber {k : ℕ} (hD : D.LevelConsistent k)
    (x y : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.chamberTransport hD x (D.levelChamber y) = D.levelTransport k hD x y := (rfl)

/-- Finite-order transport is the quotient of the two chamber values. -/
theorem levelPathProduct_eq_chamberTransport {k : ℕ} (hD : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k p =
      D.chamberTransport hD b (D.levelChamber y) *
        (D.chamberTransport hD b (D.levelChamber x))⁻¹ := by
  simp only [chamberTransport_levelChamber]
  rw [← D.levelTransport_eq_levelPathProduct hD p]
  exact eq_mul_inv_of_mul_eq (D.levelTransport_comp hD b x y).symm

/-- Lower-order chamber transports admit normalized lifts to every higher truncation.
No consistency at the higher order is needed. -/
theorem exists_chamberTransport_lifts {k l : ℕ} (hkl : k ≤ l)
    (hD : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support)) :
    ∃ t : D.LevelChamber k → d.truncatedGroup ℒ l,
      t (D.levelChamber b) = 1 ∧
        ∀ C, (d.truncationMap ℒ hkl).bchGroupMap (t C) = D.chamberTransport hD b C := by
  classical
  have hsurj : Function.Surjective (d.truncationMap ℒ hkl).bchGroupMap :=
    d.groupTower_map_surjective ℒ (CategoryTheory.homOfLE hkl).op
  choose t ht using fun C => hsurj (D.chamberTransport hD b C)
  refine ⟨Function.update t (D.levelChamber b) 1, by simp, ?_⟩
  intro C
  by_cases he : C = D.levelChamber b
  · simp [he]
  · simpa only [Function.update_of_ne he] using ht C

/-- Gauging a higher-order path by lifts of lower-order chamber transport puts its
product in the truncation kernel. At successive cutoffs this kernel is central. -/
theorem chamberLift_path_mem_ker {k l : ℕ} (hkl : k ≤ l) (hD : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    (t : D.LevelChamber k → d.truncatedGroup ℒ l)
    (ht : ∀ C, (d.truncationMap ℒ hkl).bchGroupMap (t C) = D.chamberTransport hD b C)
    {x y : WallComplement (fun j : D.active l => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    let r := WallComplement.restrictPrefunctor (fun j : D.active l => (D.wall j).support)
      (Set.inclusion (D.active_mono hkl))
    (t (D.levelChamber (r.obj y)))⁻¹ * D.levelPathProduct l p *
      t (D.levelChamber (r.obj x)) ∈ (d.truncationMap ℒ hkl).bchGroupMap.ker := by
  dsimp only
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht, ht,
    D.truncation_levelPathProduct hkl,
    D.levelPathProduct_eq_chamberTransport hD b]
  group

end Mei.DirectedDiagram
