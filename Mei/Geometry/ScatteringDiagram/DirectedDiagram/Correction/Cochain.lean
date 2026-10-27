/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Sweep
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Boundary

/-!
# Realizing swept cochains by directed correction walls

A finite family of transverse oriented cells with homogeneous wall-space
coefficients gives an actual outgoing directed diagram. The normals induce the
contraction orientations of the swept cells, and each label has pure birth
logarithm. At the retained order, the logarithmic cochain of these walls is
exactly the negative sweep of the original coefficient cochain. If the original
signed boundary vanishes, the signed boundary of this logarithmic presentation
is the original cochain, by the sweep homotopy identity. Repeated and
coincident cells retain their indices and their contributions.

The construction uses `DirectedWall.exists_cooriented_sweep`, which combines
`DirectedWallSpaces.exists_cooriented_sweep_normal` with the completed negative
exponential, and the linear map `PolyhedralCochain.sweep`. This is the signed
realization of the homogeneous swept obstruction used in Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, proof of
Theorem 2.6. The result constructs the correction family; consistency of the
union with the original walls requires the geometric boundary identities.
-/

public section

noncomputable section

open Set Module Mei BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

/-- Realize a finite homogeneous transverse cochain by outgoing swept walls.
Their normals agree with the swept orientations and their logarithmic cochain
is the negative cochain sweep. A zero coefficient gives the identity label;
every nonzero coefficient first appears at its homogeneous degree. If the source
has zero signed boundary, the logarithmic presentation bounds the source cochain.
The chosen supporting equations need not be primitive or have the prescribed sign. -/
theorem exists_sweep_correction_family [Fintype ι]
    (σ : ι → OrientedCell h 2) {n : Γ} (hn : n ∈ d.monoid)
    (htrans : ∀ j, i (ρ n) ∉ (affineSpan ℝ (σ j).carrier).direction)
    (m₀ : ι → Λ →+ ℤ)
    (h₀ : ∀ j, (h.realCharacter (m₀ j)).ker =
      (affineSpan ℝ (σ j).carrier).direction ⊔ ℝ ∙ i (ρ n))
    (k : ℕ) (hnk : d.degree n ≤ k) (c : ι → d.truncatedLie ℒ k)
    (hc : ∀ j, c j ∈ (H.truncated d k).wall n (m₀ j)) :
    ∃ E : DirectedDiagram (d := d) h H ι,
      (∀ j,
        (E.wall j).support = ((σ j).sweep (ρ n) (htrans j)).carrier ∧
        (∀ v : V, SignType.sign (h.realCharacter (E.wall j).normal v) =
          ((σ j).sweep (ρ n) (htrans j)).orientation.evalSign (fun _ : Fin 1 => v)) ∧
        n ∈ (E.wall j).ray.rayDegrees ∧
        (∃ a ∈ ℒ n, (E.wall j).label = d.expToCompletion ℒ (-a)) ∧
        (E.wall j).Outgoing ∧
        log (CompletedGroup.projection k (E.wall j).label) = -c j ∧
        ∀ l : ℕ, j ∈ E.active l ↔ c j ≠ 0 ∧ d.degree n ≤ (l : ℤ)) ∧
      (∑ j, PolyhedralCochain.mk (R := R) ((σ j).sweep (ρ n) (htrans j))
        (log (CompletedGroup.projection k (E.wall j).label))) =
        -PolyhedralCochain.sweep (ρ n)
          (∑ j, (⟨PolyhedralCochain.mk (σ j) (c j),
            PolyhedralCochain.mk_mem_transverseSubmodule (i (ρ n)) (σ j)
              (htrans j) (c j)⟩ : PolyhedralCochain.transverseSubmodule (R := R)
                (h := h) (E := d.truncatedLie ℒ k) (k := 2) (i (ρ n)))) ∧
      (PolyhedralCochain.coboundaryOfFinsupp (R := R)
          (∑ j, Finsupp.single (σ j) (c j)) = 0 →
        PolyhedralCochain.coboundaryOfFinsupp (R := R)
          (∑ j, Finsupp.single ((σ j).sweep (ρ n) (htrans j))
            (log (CompletedGroup.projection k (E.wall j).label))) =
          ∑ j, PolyhedralCochain.mk (σ j) (c j)) := by
  classical
  choose W hs hsign hray hpure hout hlog hactive using fun j =>
    DirectedWall.exists_cooriented_sweep (σ j) hn (htrans j) (m₀ j) (h₀ j) k hnk (c j) (hc j)
  refine ⟨ofFinite W, ?_, ?_, ?_⟩
  · intro j
    simp only [ofFinite_wall]
    refine ⟨hs j, hsign j, hray j, hpure j, hout j, hlog j, fun l => ?_⟩
    simpa only [mem_active, ofFinite_wall, not_or, not_lt] using not_congr (hactive j l)
  · simp only [ofFinite_wall, hlog, map_neg, Finset.sum_neg_distrib, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact (PolyhedralCochain.sweep_mk (k := 1) (ρ n) (σ j) (htrans j) (c j)).symm
  · intro hclosed
    have hsum := PolyhedralCochain.coboundaryOfFinsupp_sum_sweep_of_coboundary_eq_zero
      (ρ n) σ htrans c hclosed
    simp only [map_sum, PolyhedralCochain.coboundaryOfFinsupp_single,
      ofFinite_wall, hlog, map_neg, Finset.sum_neg_distrib]
    simpa only [map_sum, PolyhedralCochain.coboundaryOfFinsupp_single, neg_neg] using
      congrArg Neg.neg hsum

end Mei.DirectedDiagram
