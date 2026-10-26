/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.PathProduct
public import Mei.Geometry.ScatteringDiagram.KS.Completion
public import Mei.Geometry.ScatteringDiagram.KS.Chamber
public import Mei.Algebra.PositiveDegrees.Chamber

/-!
# Completed middle-factor reconstruction

The finite middle-factor reconstructions of the projections of a completed BCH
element form a compatible consistent completed diagram. Transport from any allowed
point in the positive chamber to any allowed point in the negative chamber recovers
the original group element, without finite generation of the positive monoid.
This is the reconstruction of Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open Set Mei.Convex BCHGroup

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {k : ℕ}

/-- The negative factor at a positive chamber point is the identity. -/
theorem signFactorizationEquiv_neg_of_mem_positiveChamber
    {θ : V →L[ℝ] ℝ} (hθ : θ ∈ d.monoid.positiveChamber i)
    (g : d.truncatedGroup ℒ k) :
    ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g .neg :
      d.truncatedGroup ℒ k) = 1 := by
  simpa using d.signFactorizationEquiv_symm_of_mem_positiveChamber i ℒ hθ g .neg

/-- The negative factor at a negative chamber point is the original element. -/
theorem signFactorizationEquiv_neg_of_mem_negativeChamber
    {θ : V →L[ℝ] ℝ} (hθ : θ ∈ d.monoid.negativeChamber i)
    (g : d.truncatedGroup ℒ k) :
    ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g .neg :
      d.truncatedGroup ℒ k) = g := by
  simpa using d.signFactorizationEquiv_symm_of_mem_negativeChamber i ℒ hθ g .neg

/-- The completed KS diagram reconstructed from a completed BCH group element. -/
def reconstruct (g : d.completedBCHGroup ℒ) :
    CompletedDiagram (KSSpace.continuousDual h) d ℒ (fun k => d.arrangementComplex h k) where
  diagram k := d.reconstructFinite h ℒ (CompletedGroup.projection k g)
  compatible := by
    intro k x y x' y' p q hv
    have hx : x.val = x'.val := by
      simpa using congrArg List.head? hv
    have hy : y.val = y'.val := by
      simpa [List.getLast?_eq_getLast_of_ne_nil p.vertices_ne_nil,
        List.getLast?_eq_getLast_of_ne_nil q.vertices_ne_nil] using congrArg List.getLast? hv
    let a : d.truncatedGroup ℒ k := CompletedGroup.projection k g
    let b : d.truncatedGroup ℒ (k + 1) := CompletedGroup.projection (k + 1) g
    -- The tower objects are the concrete truncated BCH groups. Naming their
    -- elements fixes this identification before rewriting the finite products.
    change (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
      ((d.reconstructFinite h ℒ b).toFiniteWallDiagram.pathProduct q) =
      (d.reconstructFinite h ℒ a).toFiniteWallDiagram.pathProduct p
    rw [d.pathProduct_reconstructFinite h ℒ b q, map_mul, map_inv,
      truncationMap_signFactorizationEquiv_symm, truncationMap_signFactorizationEquiv_symm]
    have hg : (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap b = a :=
      CompletedGroup.map_projection k (k + 1) (Nat.le_succ k) g
    rw [hg, d.pathProduct_reconstructFinite h ℒ a p, hx, hy]

/-- At each order, completed reconstruction is the existing finite reconstruction
of the projected group element. -/
@[simp]
theorem reconstruct_diagram (g : d.completedBCHGroup ℒ) (k : ℕ) :
    (d.reconstruct h ℒ g).diagram k =
      d.reconstructFinite h ℒ (CompletedGroup.projection k g) := (rfl)

/-- The reconstructed completed diagram is consistent at every finite order. -/
theorem consistent_reconstruct (g : d.completedBCHGroup ℒ) :
    (d.reconstruct h ℒ g).Consistent := by
  rw [CompletedDiagram.consistent_iff]
  intro k
  rw [reconstruct_diagram]
  exact d.consistent_reconstructFinite h ℒ (CompletedGroup.projection k g)

/-- Transport from any positive chamber point to any negative chamber point
in the reconstructed diagram is its original completed BCH group element.
Finite generation of the positive monoid is not needed. -/
theorem transport_reconstruct_of_mem_chambers (g : d.completedBCHGroup ℒ)
    (x y : CompletedDiagram.Point (fun k => d.arrangementComplex h k))
    (hx : x.val ∈ d.monoid.positiveChamber i)
    (hy : y.val ∈ d.monoid.negativeChamber i) :
    (d.reconstruct h ℒ g).transport (d.consistent_reconstruct h ℒ g) x y = g := by
  let D := d.reconstruct h ℒ g
  obtain ⟨p⟩ := CompletedDiagram.exists_path x y
  rw [D.transport_eq_pathProduct (d.consistent_reconstruct h ℒ g) p]
  apply CompletedGroup.ext
  intro k
  rw [CompletedDiagram.projection_pathProduct]
  let a : d.truncatedGroup ℒ k := CompletedGroup.projection k g
  -- Projection selects the finite diagram of this concrete truncated element.
  change (d.reconstructFinite h ℒ a).toFiniteWallDiagram.pathProduct
    ((CommonWallComplement.projectionPrefunctor k).mapPath p) = a
  rw [d.pathProduct_reconstructFinite]
  -- Common-path projection retains the same underlying dual endpoints.
  change
    ((signFactorizationEquiv ℒ (y.val.toAddMonoidHom.comp i) d k).symm a .neg :
      d.truncatedGroup ℒ k) *
    ((signFactorizationEquiv ℒ (x.val.toAddMonoidHom.comp i) d k).symm a .neg :
      d.truncatedGroup ℒ k)⁻¹ = a
  rw [d.signFactorizationEquiv_neg_of_mem_negativeChamber ℒ hy,
    d.signFactorizationEquiv_neg_of_mem_positiveChamber ℒ hx, inv_one, mul_one]

/-- Positive-to-negative degree transport in the reconstructed diagram recovers
its original completed BCH group element. -/
theorem transport_reconstruct (g : d.completedBCHGroup ℒ) :
    (d.reconstruct h ℒ g).transport (d.consistent_reconstruct h ℒ g)
      (d.reconstruct h ℒ g).degreePoint (d.reconstruct h ℒ g).negDegreePoint = g := by
  apply d.transport_reconstruct_of_mem_chambers h ℒ g
  · rw [AddSubmonoid.mem_positiveChamber]
    intro n hn hn0
    rw [CompletedDiagram.degreePoint_val]
    rw [← KSSpace.continuousDual_evaluation h, KSSpace.evaluation_degreePoint]
    exact Int.cast_pos.mpr (d.degree_pos hn hn0)
  · rw [AddSubmonoid.mem_negativeChamber]
    intro n hn hn0
    rw [CompletedDiagram.negDegreePoint_val, neg_apply]
    rw [← KSSpace.continuousDual_evaluation h, KSSpace.evaluation_degreePoint]
    exact neg_neg_of_pos (Int.cast_pos.mpr (d.degree_pos hn hn0))

/-- Distinct completed BCH elements reconstruct to distinct completed diagrams. -/
theorem reconstruct_injective : Function.Injective (d.reconstruct h ℒ) := by
  intro g g' he
  have he' :
      (⟨d.reconstruct h ℒ g, d.consistent_reconstruct h ℒ g⟩ :
        {D : CompletedDiagram (KSSpace.continuousDual h) d ℒ
          (fun k => d.arrangementComplex h k) // D.Consistent}) =
      ⟨d.reconstruct h ℒ g', d.consistent_reconstruct h ℒ g'⟩ := Subtype.ext he
  -- Package each diagram with consistency so transport rewrites dependently.
  have ht := congrArg
    (fun D => D.val.transport D.property D.val.degreePoint D.val.negDegreePoint) he'
  change (d.reconstruct h ℒ g).transport (d.consistent_reconstruct h ℒ g)
      (d.reconstruct h ℒ g).degreePoint (d.reconstruct h ℒ g).negDegreePoint =
    (d.reconstruct h ℒ g').transport (d.consistent_reconstruct h ℒ g')
      (d.reconstruct h ℒ g').degreePoint (d.reconstruct h ℒ g').negDegreePoint at ht
  rwa [d.transport_reconstruct h ℒ g, d.transport_reconstruct h ℒ g'] at ht

end Mei.PositiveDegrees
