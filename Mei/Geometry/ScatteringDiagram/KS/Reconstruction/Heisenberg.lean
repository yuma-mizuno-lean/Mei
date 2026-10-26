/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.Map
public import Mei.Algebra.Lie.Heisenberg.Completion

/-!
# Coefficient maps need not reflect equivalence

Grade the Heisenberg Lie algebra over `ℤ`, with `X` and `Y` in degree one and `Z`
in degree two. The completed exponentials `exp X * exp Y` and `exp Y * exp X` differ,
so their reconstructed completed KS diagrams are inequivalent: equivalent diagrams
have equal products along a common path from the positive to the negative degree
point, and reconstruction recovers the element as this transport.

The truncation to order one is the quotient by the center, since the degree ideal
above order one is the center (`degreeIdeal_heisenbergGrading_one`). This quotient is
abelian, so the two reconstructed diagrams have equal images under `mapDiagram`.
Thus `CompletedDiagram.mapDiagram`, which preserves equivalence
(`CompletedDiagram.Equivalent.mapDiagram`), can identify inequivalent diagrams.

The noncommutation is `exp_heisenbergX_mul_exp_heisenbergY_ne`, transported to the
completion through the order-two truncation, which is injective because the degree
ideal above order two vanishes.
-/

public section

noncomputable section

namespace Mei

open TauCeti PositiveDegrees Mei.Convex

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R] [Algebra ℚ R]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {i : ℤ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i)

/-- The reconstructed diagrams of `exp X * exp Y` and `exp Y * exp X` in the
completed Heisenberg BCH group are inequivalent over a nontrivial coefficient ring. -/
theorem not_equivalent_reconstruct_heisenberg [Nontrivial R] :
    ¬ (nonnegIntegers.reconstruct h (heisenbergGrading R)
        (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R) *
          nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R))).Equivalent
      (nonnegIntegers.reconstruct h (heisenbergGrading R)
        (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R) *
          nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R))) := by
  intro hE
  apply expToCompletion_heisenbergX_mul_expToCompletion_heisenbergY_ne R
  set D := nonnegIntegers.reconstruct h (heisenbergGrading R)
    (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R) *
      nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R))
  set F := nonnegIntegers.reconstruct h (heisenbergGrading R)
    (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R) *
      nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R))
  -- The degree points depend only on the shared arrangements, not on the labels.
  have hx : F.degreePoint = D.degreePoint := CommonWallComplement.ext (by simp)
  have hy : F.negDegreePoint = D.negDegreePoint := CommonWallComplement.ext (by simp)
  obtain ⟨p⟩ := CompletedDiagram.exists_path D.degreePoint D.negDegreePoint
  have hD := nonnegIntegers.transport_reconstruct h (heisenbergGrading R)
    (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R) *
      nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R))
  have hF := nonnegIntegers.transport_reconstruct h (heisenbergGrading R)
    (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R) *
      nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R))
  rw [hx, hy, F.transport_eq_pathProduct _ p] at hF
  rw [D.transport_eq_pathProduct _ p] at hD
  rw [← hD, ← hF]
  exact hE.pathProduct_eq p p rfl

/-- After the quotient by the center, which is the truncation to order one, the
reconstructed diagrams of `exp X * exp Y` and `exp Y * exp X` coincide. -/
theorem mapDiagram_truncation_reconstruct_heisenberg :
    (nonnegIntegers.reconstruct h (heisenbergGrading R)
        (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R) *
          nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R))).mapDiagram
        (GradedLieHom.truncation nonnegIntegers (heisenbergGrading R) 1) =
      (nonnegIntegers.reconstruct h (heisenbergGrading R)
        (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R) *
          nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R))).mapDiagram
        (GradedLieHom.truncation nonnegIntegers (heisenbergGrading R) 1) := by
  rw [mapDiagram_reconstruct, mapDiagram_reconstruct, map_mul, map_mul,
    GradedLieHom.completedMap_expToCompletion, GradedLieHom.completedMap_expToCompletion]
  congr 1
  apply Commute.eq
  apply commute_expToCompletion_of_lie_eq_zero
  rw [GradedLieHom.truncation_apply, GradedLieHom.truncation_apply, ← LieHom.map_lie,
    LieIdeal.mkQ_eq_zero, degreeIdeal_heisenbergGrading_one]
  exact lie_mem_center_heisenberg (heisenbergX R) (heisenbergY R)

end Mei
