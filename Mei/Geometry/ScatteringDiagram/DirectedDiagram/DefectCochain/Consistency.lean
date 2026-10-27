/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Transport
public import Mei.Geometry.Convex.PolyhedralCochain.Transport
import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus

/-!
# Consistency from closed crossing defects

If the central crossing-defect cochain is closed, its finite defect diagram is
consistent and the original directed transport vanishes on every adapted loop.
No joint-loop generation or higher-order consistency hypothesis is required.
The polyhedral primitive may introduce extra walls: the closed-cochain transport
theorem removes those general-position constraints from the conclusion.

The construction combines
`Quiver.Path.wallCrossingSum_loop_eq_zero_of_coboundary_eq_zero` with
`DirectedDiagram.coe_loopObstruction_eq_neg_wallCrossingSum_defect` and
`DirectedDiagram.pathProduct_crossingDefectDiagram`. It is the additive
path-independence step in Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, proof of Theorem 2.6.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
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

/-- Closed central crossing defects force trivial original transport on every
loop admissible for the adapted complex. The basepoint can lie in any chamber. -/
theorem levelPathProduct_adapted_loop_eq_one_of_coboundary_crossingDefectCochain_eq_zero
    (hc : PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht) = 0)
    {x : WallComplement (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V))}
    (p : AdmissiblePLPath x x) :
    D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).mapPath p) = 1 := by
  have hsum : ∀ {x : WallComplement (fun Q => (σ Q).carrier)}
      (p : AdmissiblePLPath x x), p.wallCrossingSum
        (fun Q => h.realCharacter (cross Q).normal) (fun Q => (cross Q).defect hk b t ht) = 0 := by
    intro x p
    exact p.wallCrossingSum_loop_eq_zero_of_coboundary_eq_zero (R := R) _ _
      (fun Q => (cross Q).sign_normal)
      (by simpa only [crossingDefectCochain_def] using hc)
  rw [show (fun Q => (σ Q).carrier) =
    (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V)) from funext hσ] at hsum
  obtain ⟨P, ⟨hP, hx⟩, _⟩ :=
    (D.adaptedComplex (k + 1)).exists_unique_mem_interior_cellsOfCodimension_zero
      (D.support_adaptedComplex (k + 1)) (by
        rw [(D.adaptedComplex (k + 1)).support_codimensionAtLeast_one_eq_iUnion_walls
          (D.support_adaptedComplex (k + 1))]
        exact fun hs => (mem_iUnion.mp hs).elim fun Q hQ => x.notMem Q hQ)
  apply (D.loopObstruction_eq_zero_iff hk _).mp
  apply Subtype.val_injective
  rw [coe_loopObstruction_eq_neg_wallCrossingSum_defect σ hσ cross hk b t ht p ⟨P, hP⟩ hx]
  simpa only [AddMonoidHom.map_wallCrossingSum, map_zero, neg_zero,
    LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap, LieIdeal.incl_apply,
    ZeroMemClass.coe_zero] using congrArg Neg.neg
      (congrArg (d.truncationMap ℒ (Nat.le_succ k)).ker.incl.toLinearMap.toAddMonoidHom
        (hsum p))

/-- Closedness of the crossing-defect cochain implies consistency of its finite
central defect diagram. Thus its gauged products depend only on endpoints. -/
theorem crossingDefectDiagram_consistent_of_coboundary_eq_zero
    (hc : PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht) = 0) :
    (crossingDefectDiagram σ hσ cross hk b t ht).Consistent := by
  apply (FiniteWallDiagram.consistent_iff_loops _).mpr
  intro x p
  obtain ⟨P, ⟨hP, hx⟩, _⟩ :=
    (D.adaptedComplex (k + 1)).exists_unique_mem_interior_cellsOfCodimension_zero
      (D.support_adaptedComplex (k + 1)) (by
        rw [(D.adaptedComplex (k + 1)).support_codimensionAtLeast_one_eq_iUnion_walls
          (D.support_adaptedComplex (k + 1))]
        exact fun hs => (mem_iUnion.mp hs).elim fun Q hQ => x.notMem Q hQ)
  rw [pathProduct_crossingDefectDiagram σ hσ cross hk b t ht p ⟨P, hP⟩ ⟨P, hP⟩ hx hx,
    levelPathProduct_adapted_loop_eq_one_of_coboundary_crossingDefectCochain_eq_zero
      σ hσ cross hk b t ht hc p]
  simp

end Mei.DirectedDiagram
