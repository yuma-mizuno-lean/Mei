/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall.Degree.Basic
public import Mei.Algebra.Lie.Heisenberg.Completion
public import Mei.Algebra.Lie.Heisenberg.Ray
public import Mei.Algebra.Lie.Skew.Ray

/-!
# Examples of degree-indexed walls

* *Heisenberg walls.* In a KS space over the degree lattice `ℤ` with the nonnegative integers
  as positive degrees, grade the Heisenberg Lie algebra by `heisenbergGrading`. The hyperplane
  walls of degree one labelled by `exp X` and `exp Y` (`heisenbergXWall`, `heisenbergYWall`) and
  of the nonprimitive degree two labelled by `exp Z` (`heisenbergZWall`) are degree-indexed
  walls, all reindexed by one supported ray (`ray_heisenbergYWall`, `ray_heisenbergZWall`). The
  walls of `exp X` and `exp Y` have the same support, but their labels do not commute over a
  nontrivial coefficient ring (`not_commute_label_heisenbergXWall_heisenbergYWall`). So the
  abelian-ray hypothesis of `DegreeIndexedWall.commute_label` cannot be dropped; the Heisenberg
  grading indeed fails it (`not_isAbelianRays_heisenbergGrading`).
* *Skew ray walls.* For a skew form `β` on a free degree lattice `Γ`, a nonzero allowed degree
  `n` and a power series `f`, the hyperplane wall of `n` labelled by the ray label `rayExp f`
  is a degree-indexed wall (`rayExpWall`). For every `j`, the walls of `n` and of `(j + 1) • n`
  are reindexed by the same supported ray (`ray_rayExpWall_succ_nsmul`), have the same support
  (`support_rayExpWall_succ_nsmul`), and their labels commute by the abelian rays of the skew
  grading (`commute_label_rayExpWall_succ_nsmul`).

The skew ray labels are the wall-crossing automorphisms of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), whose walls are indexed by
possibly nonprimitive degrees.
-/

public section

noncomputable section

namespace Mei.DegreeIndexedWall.Examples

open TauCeti PositiveDegrees

/-! ### Heisenberg walls -/

section Heisenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R] [Algebra ℚ R]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {i : (ℤ →+ ℤ) →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i} (s : KSSpace h)

/-- The hyperplane wall of degree one labelled by `exp X`. -/
def heisenbergXWall : DegreeIndexedWall s nonnegIntegers (heisenbergGrading R) :=
  hyperplane s 1 (mem_nonnegIntegers_monoid.mpr zero_le_one) one_ne_zero
    (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R))
    (nonnegIntegers.logComponent_expToCompletion_eq_zero_of_mem _ (heisenbergX_mem_grading R))

/-- The hyperplane wall of degree one labelled by `exp Y`. -/
def heisenbergYWall : DegreeIndexedWall s nonnegIntegers (heisenbergGrading R) :=
  hyperplane s 1 (mem_nonnegIntegers_monoid.mpr zero_le_one) one_ne_zero
    (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R))
    (nonnegIntegers.logComponent_expToCompletion_eq_zero_of_mem _ (heisenbergY_mem_grading R))

/-- The hyperplane wall of the nonprimitive degree two labelled by `exp Z`. -/
def heisenbergZWall : DegreeIndexedWall s nonnegIntegers (heisenbergGrading R) :=
  hyperplane s 2 (mem_nonnegIntegers_monoid.mpr zero_le_two) two_ne_zero
    (nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergZ R))
    (nonnegIntegers.logComponent_expToCompletion_eq_zero_of_mem _ (heisenbergZ_mem_grading R))

@[simp]
theorem heisenbergXWall_degree : (heisenbergXWall R s).degree = 1 := by
  rw [heisenbergXWall, hyperplane_degree]

@[simp]
theorem heisenbergYWall_degree : (heisenbergYWall R s).degree = 1 := by
  rw [heisenbergYWall, hyperplane_degree]

@[simp]
theorem heisenbergZWall_degree : (heisenbergZWall R s).degree = 2 := by
  rw [heisenbergZWall, hyperplane_degree]

/-- The walls of `exp X` and `exp Y` are reindexed by the same supported ray. -/
theorem ray_heisenbergYWall : (heisenbergYWall R s).ray = (heisenbergXWall R s).ray :=
  (heisenbergYWall R s).ray_eq_of_degree_mem_rayDegrees (by
    simpa using (heisenbergXWall R s).degree_mem_rayDegrees)

/-- The wall of `exp Z`, of the nonprimitive degree two, is reindexed by the supported ray of
the degree-one walls. -/
theorem ray_heisenbergZWall : (heisenbergZWall R s).ray = (heisenbergXWall R s).ray :=
  (heisenbergZWall R s).ray_eq_of_degree_mem_rayDegrees (by
    simpa using SupportedRay.succ_nsmul_mem_rayDegrees
      (heisenbergXWall R s).degree_mem_rayDegrees 1)

/-- The walls of `exp X` and `exp Y` have the same support, the hyperplane of degree one, but
their labels do not commute over a nontrivial coefficient ring. -/
theorem not_commute_label_heisenbergXWall_heisenbergYWall [Nontrivial R] :
    (heisenbergXWall R s).support = (heisenbergYWall R s).support ∧
      ¬ Commute (heisenbergXWall R s).label (heisenbergYWall R s).label := by
  refine ⟨by simp [heisenbergXWall, heisenbergYWall], fun hc => ?_⟩
  apply expToCompletion_heisenbergX_mul_expToCompletion_heisenbergY_ne R
  simpa [heisenbergXWall, heisenbergYWall] using hc.eq

end Heisenberg

/-! ### Skew ray walls -/

section Skew

open PowerSeries SkewLieAlgebra

variable {R Γ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {i : (Γ →+ ℤ) →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i} (s : KSSpace h)
  {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

/-- The hyperplane wall of a nonzero allowed degree `n` labelled by the ray label `rayExp f`,
whose logarithm `∑_{j ≥ 1} f_j X_{jn}` lies on the positive multiples of `n`. -/
def rayExpWall (f : R⟦X⟧) : DegreeIndexedWall s d (positiveGrading β hβ d) :=
  hyperplane s n hn hn0 (rayExp β hβ hn hn0 f)
    (fun _ hm => logComponent_rayExp_eq_zero_of_forall_ne β hβ hn hn0 f hm)

@[simp]
theorem rayExpWall_degree (f : R⟦X⟧) : (rayExpWall β hβ s hn hn0 f).degree = n := by
  rw [rayExpWall, hyperplane_degree]

@[simp]
theorem rayExpWall_support (f : R⟦X⟧) :
    (rayExpWall β hβ s hn hn0 f).support = LinearMap.ker (s.normal n) := by
  rw [rayExpWall, hyperplane_support]

@[simp]
theorem rayExpWall_label (f : R⟦X⟧) :
    (rayExpWall β hβ s hn hn0 f).label = rayExp β hβ hn hn0 f := by
  rw [rayExpWall, hyperplane_label]

variable [Module.Free ℤ Γ] (j : ℕ)

/-- The walls of `n` and of `(j + 1) • n` are reindexed by the same supported ray. -/
theorem ray_rayExpWall_succ_nsmul (f g : R⟦X⟧) :
    (rayExpWall β hβ s (d.monoid.nsmul_mem hn (j + 1)) (d.succ_nsmul_ne_zero hn hn0 j) g).ray =
      (rayExpWall β hβ s hn hn0 f).ray :=
  DegreeIndexedWall.ray_eq_of_degree_mem_rayDegrees _ (by
    simpa using SupportedRay.succ_nsmul_mem_rayDegrees
      (rayExpWall β hβ s hn hn0 f).degree_mem_rayDegrees j)

/-- The walls of `n` and of `(j + 1) • n` have the same support. -/
theorem support_rayExpWall_succ_nsmul (f g : R⟦X⟧) :
    (rayExpWall β hβ s (d.monoid.nsmul_mem hn (j + 1)) (d.succ_nsmul_ne_zero hn hn0 j) g).support =
      (rayExpWall β hβ s hn hn0 f).support := by
  -- Both supports are cut out by the normal of the common ray generator.
  have h₁ := (rayExpWall β hβ s hn hn0 f).ker_normal_generator
  have h₂ := (rayExpWall β hβ s (d.monoid.nsmul_mem hn (j + 1))
    (d.succ_nsmul_ne_zero hn hn0 j) g).ker_normal_generator
  rw [ray_rayExpWall_succ_nsmul β hβ s hn hn0 j f g, h₁, rayExpWall_degree,
    rayExpWall_degree] at h₂
  rw [rayExpWall_support, rayExpWall_support, h₂]

/-- The labels of the walls of `n` and of `(j + 1) • n` commute, by the abelian rays of the
skew grading. -/
theorem commute_label_rayExpWall_succ_nsmul (f g : R⟦X⟧) :
    Commute (rayExpWall β hβ s hn hn0 f).label
      (rayExpWall β hβ s (d.monoid.nsmul_mem hn (j + 1)) (d.succ_nsmul_ne_zero hn hn0 j) g).label :=
  DegreeIndexedWall.commute_label _ _
    (congrArg (affineSpan ℝ) (support_rayExpWall_succ_nsmul β hβ s hn hn0 j f g).symm)

end Skew

end Mei.DegreeIndexedWall.Examples
