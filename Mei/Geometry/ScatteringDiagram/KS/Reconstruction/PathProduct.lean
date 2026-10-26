/-
Copyright (c) 2026 The Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mei contributors
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.WallCrossing
public import Mei.Geometry.ScatteringDiagram.LocalProduct

/-!
# Global transport in finite middle-factor reconstruction

The local crossing formula and the local constancy of sign factors off the
arrangement walls determine every path product. This proves consistency directly
from sign factorization, as in Bridgeland's Lemma 3.2, §3.4 of
*Scattering diagrams, Hall algebras and stability conditions*
([arXiv:1603.00416v4](https://arxiv.org/html/1603.00416v4#S3.SS4)).
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.PositiveDegrees

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {k : ℕ}

/-- The reconstructed product on any admissible path is the quotient of the
negative sign factors at its endpoints, with the target factor on the left. -/
theorem pathProduct_reconstructFinite (g : d.truncatedGroup ℒ k)
    {x y : WallComplement
      (fun P : (d.arrangementComplex h k).walls => (P : Set (V →L[ℝ] ℝ)))}
    (p : AdmissiblePLPath x y) :
    (d.reconstructFinite h ℒ g).toFiniteWallDiagram.pathProduct p =
      ((signFactorizationEquiv ℒ (y.val.toAddMonoidHom.comp i) d k).symm g .neg :
        d.truncatedGroup ℒ k) *
      ((signFactorizationEquiv ℒ (x.val.toAddMonoidHom.comp i) d k).symm g .neg :
        d.truncatedGroup ℒ k)⁻¹ := by
  exact (d.reconstructFinite h ℒ g).toFiniteWallDiagram.pathProduct_eq_mul_inv_of_local
    (fun θ hθ => d.eventually_signFactor_eq_of_notMem_arrangementComplex_walls h ℒ hθ g .neg)
    (fun P θ hθP hθ => by
      obtain ⟨ε, hε, hproduct⟩ :=
        d.exists_radius_pathProduct_reconstructFinite_toPath h ℒ hθP hθ
      exact ⟨ε, hε, hproduct g⟩) p

/-- Middle-factor reconstruction is consistent at every finite cutoff. -/
theorem consistent_reconstructFinite (g : d.truncatedGroup ℒ k) :
    (d.reconstructFinite h ℒ g).toFiniteWallDiagram.Consistent := by
  rw [FiniteWallDiagram.consistent_def]
  intro x y p q
  rw [d.pathProduct_reconstructFinite h ℒ g p, d.pathProduct_reconstructFinite h ℒ g q]

end Mei.PositiveDegrees
