/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.HomogeneousFactor
public import Mei.Algebra.PositiveDegrees.Naturality

/-!
# Homogeneous logarithms under completed graded maps

The logarithmic coefficient of the image of a completed BCH label is the finite
sum of the images of its source coefficients over the target degree fiber. The
source cutoff is controlled by the positive degree map's modulus; its fibers
need not be finite. For an injective degree map, coefficients and homogeneous
factors commute with the completed map. In particular, degree-preserving
coefficient maps commute with homogeneous splitting, even when they kill labels.

The comparison identifies BCH exponential coordinates with the existing filtered
linear completion map. The component formulas then use
`PositiveDegrees.completionComponent_completionMap_eq_sum` and
`PositiveDegrees.completionComponent_completionMap_of_injective`. No abelian-ray
or nilpotency assumption on the original Lie algebras is needed.
-/

public noncomputable section

universe u

namespace Mei.GradedLieHom

variable {N M R : Type*} {L L' : Type u}
  [AddCommMonoid N] [AddCommMonoid M] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [DecidableEq M]
  {d : PositiveDegrees N} {e : PositiveDegrees M}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ]
  {T : PositiveDegreeMap d e} (f : GradedLieHom T ℒ ℳ)

local notation "F" =>
  LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
local notation "G" =>
  LieIdeal.completionFiltration (e.degreeIdeal ℳ) (e.degreeIdeal_antitone ℳ)

open Classical in
/-- Under arbitrary regrading, a target logarithmic coefficient is the sum over
its source degree fiber inside the cutoff prescribed by the modulus. Any target
cutoff retaining that degree suffices. Degrees may merge and coefficients may vanish. -/
theorem logComponent_completedMap_eq_sum (g : d.completedBCHGroup ℒ)
    (m : M) (k : ℕ) (hm : e.degree m ≤ k) :
    (e.logComponent ℳ (f.completedMap g) m : L') =
      ∑ n ∈ (d.finite_cutoff (T.modulus k)).toFinset with T n = m,
        f (d.logComponent ℒ g n : L) := by
  simp only [PositiveDegrees.logComponent_def, f.completedBCHExp_symm_completedMap]
  exact d.completionComponent_completionMap_eq_sum e ℒ ℳ F G
    (fun k => d.degreeIdeal_toSubmodule ℒ k) (fun k => e.degreeIdeal_toSubmodule ℳ k)
    f.toLieHom.toLinearMap T (fun _ _ hx => f.map_mem hx)
    T.modulus T.monotone_modulus (fun k _ hx => f.map_mem_degreeIdeal k hx)
    (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn)) m k hm _

/-- For injective regrading, a logarithmic coefficient of the completed image is
the image of that source coefficient. Injectivity of the Lie map is unnecessary. -/
theorem logComponent_completedMap_of_injective (hT : Function.Injective T)
    (g : d.completedBCHGroup ℒ) (n : N) :
    (e.logComponent ℳ (f.completedMap g) (T n) : L') =
      f (d.logComponent ℒ g n : L) := by
  simp only [PositiveDegrees.logComponent_def, f.completedBCHExp_symm_completedMap]
  exact d.completionComponent_completionMap_of_injective e ℒ ℳ F G
    (fun k => d.degreeIdeal_toSubmodule ℒ k) (fun k => e.degreeIdeal_toSubmodule ℳ k)
    f.toLieHom.toLinearMap T (fun _ _ hx => f.map_mem hx)
    T.modulus T.monotone_modulus (fun k _ hx => f.map_mem_degreeIdeal k hx) hT n _

/-- Homogeneous splitting commutes with a completed map whose degree map is
injective, including regradings with different cutoff functions. -/
theorem completedMap_homogeneousFactor_of_injective (hT : Function.Injective T)
    (g : d.completedBCHGroup ℒ) (n : N) :
    f.completedMap (d.homogeneousFactor ℒ g n) =
      e.homogeneousFactor ℳ (f.completedMap g) (T n) := by
  rw [PositiveDegrees.homogeneousFactor_def, PositiveDegrees.homogeneousFactor_def,
    completedMap_expToCompletion, f.logComponent_completedMap_of_injective hT]

variable {𝓝 : N → Submodule R L'} [GradedLieAlgebra 𝓝] [IsPositiveGrading d 𝓝]
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ 𝓝)

/-- A degree-preserving coefficient map commutes with logarithmic coefficients. -/
@[simp]
theorem logComponent_completedMap (g : d.completedBCHGroup ℒ) (n : N) :
    (d.logComponent 𝓝 (f.completedMap g) n : L') =
      f (d.logComponent ℒ g n : L) := by
  have he := f.logComponent_completedMap_of_injective
    (fun _ _ h => by simpa only [PositiveDegreeMap.id_apply] using h) g n
  have hn : (PositiveDegreeMap.id d).toAddMonoidHom n = n :=
    PositiveDegreeMap.id_apply n
  rw [hn] at he
  exact he

/-- A degree-preserving coefficient map commutes with every homogeneous factor,
even when that factor becomes the identity after specialization. -/
@[simp]
theorem completedMap_homogeneousFactor (g : d.completedBCHGroup ℒ) (n : N) :
    f.completedMap (d.homogeneousFactor ℒ g n) =
      d.homogeneousFactor 𝓝 (f.completedMap g) n := by
  simpa only [PositiveDegreeMap.id_apply] using
    f.completedMap_homogeneousFactor_of_injective
      (fun _ _ h => by simpa only [PositiveDegreeMap.id_apply] using h) g n

end Mei.GradedLieHom
