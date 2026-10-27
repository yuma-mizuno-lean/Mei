/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Transport
public import Mei.Geometry.Convex.PolyhedralCochain.Transport
public import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus

/-!
# Closed crossing-defect cochains give consistent defect diagrams

When the central crossing-defect cochain is closed, the finite diagram of its
negative exponentials is consistent. Its loop products are the actual directed
loop products conjugated by chamber lifts. Closedness therefore kills the
higher-order obstruction on every adapted loop, even if a polyhedral primitive
introduces facets absent from the adapted complex.

This applies `Quiver.Path.wallCrossingSum_eq_zero_of_coboundary_eq_zero` to the
successive-kernel coefficients and uses
`DirectedDiagram.pathProduct_crossingDefectDiagram` to compare with the given
directed transport. It is the additive consistency step in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6. Consistency of a corrected stage still requires proving
closedness of its total crossing-defect cochain.
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

/-- Closedness of the actual kernel-valued crossing-defect cochain implies
consistency of its finite exponential diagram. Only consistency at the previous
cutoff is assumed of the original directed diagram. -/
theorem crossingDefectDiagram_consistent_of_coboundary_eq_zero
    (hc : PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht) = 0) :
    (crossingDefectDiagram σ hσ cross hk b t ht).Consistent := by
  apply (FiniteWallDiagram.consistent_iff_loops _).mpr
  intro x p
  have hx : x.val ∉ ((D.adaptedComplex (k + 1)).codimensionAtLeast 1).support := by
    rw [(D.adaptedComplex (k + 1)).support_codimensionAtLeast_one_eq_iUnion_walls
      (D.support_adaptedComplex (k + 1))]
    exact fun hx => let ⟨Q, hQ⟩ := mem_iUnion.mp hx; x.notMem Q hQ
  obtain ⟨P, ⟨hP, hxP⟩, _⟩ :=
    (D.adaptedComplex (k + 1)).exists_unique_mem_interior_cellsOfCodimension_zero
      (D.support_adaptedComplex (k + 1)) hx
  have hsum : p.wallCrossingSum (fun Q => h.realCharacter (cross Q).normal)
      (fun Q => (cross Q).defect hk b t ht) = 0 := by
    have he : ∀ {x : WallComplement (fun Q => (σ Q).carrier)}
        (q : AdmissiblePLPath x x),
        q.wallCrossingSum (fun Q => h.realCharacter (cross Q).normal)
          (fun Q => (cross Q).defect hk b t ht) = 0 := by
      intro x q
      exact q.wallCrossingSum_eq_zero_of_coboundary_eq_zero _ _
        (fun Q => (cross Q).ker_normal) (fun Q _ => (cross Q).sign_normal)
        (by simpa only [crossingDefectCochain_def] using hc)
    have hcarriers : (fun Q => (σ Q).carrier) =
        (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V)) := funext hσ
    rw [hcarriers] at he
    exact he p
  apply log_injective
  rw [pathProduct_crossingDefectDiagram σ hσ cross hk b t ht p ⟨P, hP⟩ ⟨P, hP⟩ hxP hxP,
    log_inv_mul_levelPathProduct_mul_eq_neg_wallCrossingSum_defect
      σ hσ cross hk b t ht p ⟨P, hP⟩ ⟨P, hP⟩ hxP hxP, log_one]
  have he := congrArg
    (d.truncationMap ℒ (Nat.le_succ k)).ker.incl.toLinearMap.toAddMonoidHom hsum
  rw [AddMonoidHom.map_wallCrossingSum, map_zero] at he
  exact neg_eq_zero.mpr he

end Mei.DirectedDiagram
