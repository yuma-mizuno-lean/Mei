/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Ray
public import Mei.Algebra.Lie.BCH.Subgroup
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Completed supported-ray subgroups

The completed ray subgroup consists of compatible BCH labels whose finite
logarithms are supported on one primitive ray. Finite quotient maps carry ray
algebras and their BCH subgroups onto the corresponding lower-order objects.
Distinct ray subgroups have trivial intersection. Under `IsAbelianRays`, labels
in one completed ray subgroup commute, so coincident supports can be merged
without choosing an order, including labels indexed by different nonprimitive
multiples of the same ray.

The construction uses `Mei.rayLieSubalgebra`, Mathlib's subgroup intersections
and inverse images, and `LieSubalgebra.bchSubgroup`. Commutation follows from
`Mei.BCHGroup.commute_exp_of_lie_eq_zero` at every finite order. The levelwise
subgroup, support-bound and commutation arguments follow
`Mei.Geometry.ScatteringDiagram.WallSpace.Group`, replacing wall spaces with
all homogeneous pieces on the ray.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Finite ray BCH subgroups map onto the corresponding lower-order subgroup. -/
theorem map_bchSubgroup_rayLieSubalgebra (w : SupportedRay d)
    {k l : ℕ} (h : k ≤ l) :
    (rayLieSubalgebra (d.truncatedGrading ℒ l) w).bchSubgroup.map
        (d.truncationMap ℒ h).bchGroupMap =
      (rayLieSubalgebra (d.truncatedGrading ℒ k) w).bchSubgroup := by
  rw [← LieSubalgebra.bchSubgroup_map, map_rayLieSubalgebra_truncationMap]

/-- Completed labels whose logarithms at every cutoff are supported on one ray. -/
def completedRaySubgroup (w : SupportedRay d) : Subgroup (d.completedBCHGroup ℒ) :=
  ⨅ k, (rayLieSubalgebra (d.truncatedGrading ℒ k) w).bchSubgroup.comap
    (CompletedGroup.projection k)

/-- Ray subgroup membership is detected by the support of every finite logarithm. -/
@[simp]
theorem mem_completedRaySubgroup (w : SupportedRay d) (g : d.completedBCHGroup ℒ) :
    g ∈ d.completedRaySubgroup ℒ w ↔ ∀ k,
      BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) ∈
        rayLieSubalgebra (d.truncatedGrading ℒ k) w := by
  simp only [completedRaySubgroup, Subgroup.mem_iInf]
  exact forall_congr' fun k => LieSubalgebra.mem_bchSubgroup _ _

/-- Exponentials of elements of the original ray Lie algebra lie in its completed subgroup. -/
theorem expToCompletion_mem_completedRaySubgroup {w : SupportedRay d} {x : L}
    (hx : x ∈ rayLieSubalgebra ℒ w) :
    d.expToCompletion ℒ x ∈ d.completedRaySubgroup ℒ w := by
  rw [mem_completedRaySubgroup]
  intro k
  rw [projection_expToCompletion, BCHGroup.log_exp, ← map_rayLieSubalgebra_mkQ]
  exact ⟨x, hx, rfl⟩

/-- Distinct primitive rays have no common nonidentity completed label. -/
theorem disjoint_completedRaySubgroup [HasUniqueDiv N] {v w : SupportedRay d} (h : v ≠ w) :
    Disjoint (d.completedRaySubgroup ℒ v) (d.completedRaySubgroup ℒ w) := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro g hg
  apply CompletedGroup.ext
  intro k
  rw [map_one]
  apply BCHGroup.log_injective (L := d.truncatedLie ℒ k)
  have hz : BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) = 0 :=
    (disjoint_rayLieSubalgebra (d.truncatedGrading ℒ k) h).le_bot
      ⟨(d.mem_completedRaySubgroup ℒ v g).mp hg.1 k,
        (d.mem_completedRaySubgroup ℒ w g).mp hg.2 k⟩
  exact hz.trans (BCHGroup.log_one (L := d.truncatedLie ℒ k)).symm

/-- A ray with no actual degree at or below the cutoff has trivial projection there. -/
theorem projection_eq_one_of_notMem_raysAtOrder {w : SupportedRay d}
    {g : d.completedBCHGroup ℒ} (hg : g ∈ d.completedRaySubgroup ℒ w) (k : ℕ)
    (hw : w ∉ d.raysAtOrder k) : CompletedGroup.projection k g = 1 := by
  have hle : rayLieSubalgebra ℒ w ≤ (d.degreeIdeal ℒ k).toLieSubalgebra := by
    apply (rayLieSubalgebra_le_iff ℒ w _).mpr
    intro n hn
    apply d.le_degreeIdeal ℒ
    exact lt_of_not_ge fun hnk => hw (d.mem_raysAtOrder.mpr ⟨n, hn, hnk⟩)
  obtain ⟨x, hx, he⟩ := (LieSubalgebra.mem_map _ _ _).mp
    ((d.map_rayLieSubalgebra_mkQ ℒ w k).symm ▸
      (d.mem_completedRaySubgroup ℒ w g).mp hg k)
  apply BCHGroup.log_injective (L := d.truncatedLie ℒ k)
  exact (he.symm.trans ((d.degreeIdeal ℒ k).mkQ_eq_zero.mpr (hle hx))).trans
    (BCHGroup.log_one (L := d.truncatedLie ℒ k)).symm

/-- A choice of one completed label on each supported ray is finite at every order. -/
theorem hasFiniteSupport_completedRaySubgroup [HasUniqueDiv N]
    (g : ∀ w : SupportedRay d, d.completedRaySubgroup ℒ w) :
    CompletedGroup.HasFiniteSupport (fun w => (g w : d.completedBCHGroup ℒ)) := by
  intro k
  apply (d.finite_raysAtOrder k).subset
  intro w hw
  by_contra hn
  exact hw (d.projection_eq_one_of_notMem_raysAtOrder ℒ (g w).property k hn)

/-- Labels on one supported ray commute whenever the ray Lie algebras are abelian. -/
theorem commute_of_mem_completedRaySubgroup [IsAbelianRays d ℒ]
    {w : SupportedRay d} {g h : d.completedBCHGroup ℒ}
    (hg : g ∈ d.completedRaySubgroup ℒ w) (hh : h ∈ d.completedRaySubgroup ℒ w) :
    Commute g h := by
  apply CompletedGroup.ext
  intro k
  rw [map_mul, map_mul]
  have hc := BCHGroup.commute_exp_of_lie_eq_zero _ _
    (lie_eq_zero_of_mem_rayLieSubalgebra (d.truncatedGrading ℒ k)
      ((d.mem_completedRaySubgroup ℒ w g).mp hg k)
      ((d.mem_completedRaySubgroup ℒ w h).mp hh k))
  rw [BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g),
    BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k h)] at hc
  exact hc.eq

/-- Abelian rays give abelian completed ray subgroups. -/
instance completedRaySubgroup_isMulCommutative [IsAbelianRays d ℒ] (w : SupportedRay d) :
    IsMulCommutative (d.completedRaySubgroup ℒ w) :=
  IsMulCommutative.of_setLike_mul_comm fun _ hg _ hh =>
    (d.commute_of_mem_completedRaySubgroup ℒ hg hh).eq

end Mei.PositiveDegrees
