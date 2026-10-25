/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Hom
public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import Mei.Algebra.PositiveDegrees.Subquotient

/-!
# Gradings on homogeneous Lie subalgebras

A Lie subalgebra stable under homogeneous projection inherits the ambient Lie
grading: its degree-`i` piece is the inverse image of the ambient degree-`i` piece
under inclusion. In particular, every vanishing ambient piece remains zero, so
positive gradings restrict to homogeneous Lie subalgebras.
The inherited degree ideals are the inverse images of the ambient degree ideals.

`LieSubalgebra.gradedLieAlgebra` supplies the inherited structure for use as a
local instance. The direct-sum decomposition is Tau Ceti's
`TauCeti.DirectSum.Decomposition.restrict`; bracket compatibility is inherited
from the ambient `GradedLieAlgebra`. Membership and homogeneous projections use
the existing `Submodule.mem_comap` and `DirectSum.map_decompose_restrict` APIs.
-/

public section

namespace LieSubalgebra

variable {ι R L : Type*} [DecidableEq ι] [AddCommMonoid ι]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  (K : LieSubalgebra R L) (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

/-- A homogeneous Lie subalgebra inherits a Lie grading by the inverse images of
the ambient pieces. Use `letI := K.gradedLieAlgebra ℒ hK` to install the grading. -/
@[instance_reducible]
noncomputable def gradedLieAlgebra (hK : DirectSum.SetLike.IsHomogeneous ℒ K) :
    GradedLieAlgebra (fun i => (ℒ i).comap K.incl.toLinearMap) where
  toDecomposition := TauCeti.DirectSum.Decomposition.restrict ℒ _ K.incl.toLinearMap
    Subtype.val_injective (fun _ _ => Iff.rfl) (fun i x =>
      ⟨⟨_, hK i x.property⟩, rfl⟩)
  toGradedBracket := inferInstance

omit [DecidableEq ι] [GradedLieAlgebra ℒ] in
/-- The pieces inherited by a Lie subalgebra have positive support. -/
instance instIsPositiveGrading (d : Mei.PositiveDegrees ι) [Mei.IsPositiveGrading d ℒ] :
    Mei.IsPositiveGrading d (fun i => (ℒ i).comap K.incl.toLinearMap) :=
  Mei.IsPositiveGrading.comap d ℒ K.incl.toLinearMap Subtype.val_injective

/-- The cutoff ideal of a homogeneous Lie subalgebra is the preimage of the ambient cutoff.
Together with the inherited decomposition, this identifies its positive degree filtration. -/
theorem degreeIdeal_eq_comap (d : Mei.PositiveDegrees ι) [Mei.IsPositiveGrading d ℒ]
    (hK : DirectSum.SetLike.IsHomogeneous ℒ K) (k : ℕ) :
    let := K.gradedLieAlgebra ℒ hK
    d.degreeIdeal (fun i => (ℒ i).comap K.incl.toLinearMap) k =
      (d.degreeIdeal ℒ k).comap K.incl := by
  let := K.gradedLieAlgebra ℒ hK
  apply LieSubmodule.toSubmodule_injective
  simp only [Mei.PositiveDegrees.degreeIdeal_toSubmodule, LieIdeal.comap_toSubmodule]
  exact d.degreeSubmodule_comap ℒ _ K.incl.toLinearMap Subtype.val_injective
    (fun _ _ hx => Submodule.mem_comap.mp hx) k

end LieSubalgebra
