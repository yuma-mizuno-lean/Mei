/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Skew.Basic
public import Mei.Algebra.Lie.Graded.Ray
public import Mei.Algebra.Lie.Graded.Subalgebra
public import Mathlib.LinearAlgebra.Finsupp.Span

/-!
# Positive gradings and abelian rays of skew Lie algebras

The skew Lie algebra has one homogeneous generator in each exponent degree.
Restricting to the nonzero degrees of a positive monoid gives a positively graded
Lie algebra, so its degree quotients and completed BCH group use the existing
positive-grading constructions. Its supported-ray subalgebras are abelian,
including when the ambient primitive vector is outside the positive monoid.

The decomposition follows `Mei.LogarithmicVectorField.grade`, using Mathlib's
independence and spanning of `Finsupp.lsingle`; restriction uses
`supportedLieSubalgebra` and `LieSubalgebra.gradedLieAlgebra`.
The skew bracket and abelian-ray observation follow Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt)

/-- The exponent-`n` piece of the skew Lie algebra. -/
def grade (n : Γ) : Submodule R (SkewLieAlgebra β hβ) :=
  LinearMap.range (single β hβ n)

/-- Each exponent piece is the range of its homogeneous inclusion. -/
theorem grade_def : grade β hβ = fun n => LinearMap.range (single β hβ n) := (rfl)

/-- Homogeneous elements are scalar multiples of the corresponding generator. -/
theorem mem_grade_iff (n : Γ) (x : SkewLieAlgebra β hβ) :
    x ∈ grade β hβ n ↔ ∃ r, single β hβ n r = x := Iff.rfl

instance : SetLike.GradedBracket (grade β hβ) (grade β hβ) where
  bracket_mem := by
    rintro n m x y ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨_, (single_bracket_single β hβ n m r s).symm⟩

/-- The skew generators give an internal exponent grading compatible with the bracket. -/
noncomputable instance [DecidableEq Γ] : GradedLieAlgebra (grade β hβ) where
  toDecomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · simpa only [grade_def, single_def, LinearMap.range_comp] using
        ((toFinsupp β hβ).symm.toLinearMap.iSupIndep_map
          (toFinsupp β hβ).symm.injective (iSupIndep_range_lsingle Γ R R))
    · simp only [grade_def, single_def, LinearMap.range_comp, ← Submodule.map_iSup,
        Finsupp.iSup_lsingle_range]
      simp [LinearMap.range_eq_top.mpr (toFinsupp β hβ).symm.surjective]
  toGradedBracket := inferInstance

/-- Homogeneous projection extracts the exponent coefficient. -/
@[simp]
theorem decompose_grade [DecidableEq Γ] (x : SkewLieAlgebra β hβ) (n : Γ) :
    (DirectSum.decompose (grade β hβ) x n : SkewLieAlgebra β hβ) =
      single β hβ n (toFinsupp β hβ x n) := by
  induction x using induction_on β hβ with
  | h0 => simp
  | hs m r =>
    have hm : single β hβ m r ∈ grade β hβ m := ⟨r, rfl⟩
    by_cases h : m = n
    · subst m; simp [DirectSum.decompose_of_mem_same _ hm]
    · simp [DirectSum.decompose_of_mem_ne _ hm h, Finsupp.single_eq_of_ne (Ne.symm h)]
  | ha x y hx hy => simp [hx, hy]

variable (d : PositiveDegrees Γ)

/-- Every supported ray of the skew Lie algebra is abelian. -/
instance : IsAbelianRays d (grade β hβ) := by
  apply (isAbelianRays_iff (grade β hβ)).mpr
  intro w n m hn hm x hx y hy
  obtain ⟨_, a, _, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
  obtain ⟨_, b, _, rfl⟩ := SupportedRay.mem_rayDegrees.mp hm
  obtain ⟨r, rfl⟩ := (mem_grade_iff β hβ _ x).mp hx
  obtain ⟨s, rfl⟩ := (mem_grade_iff β hβ _ y).mp hy
  exact single_zsmul_bracket_single_zsmul β hβ w.generator a b r s

/-- The skew Lie algebra supported on the nonzero degrees of a positive monoid. -/
def positiveLieAlgebra : LieSubalgebra R (SkewLieAlgebra β hβ) :=
  supportedLieSubalgebra (grade β hβ)
    { carrier := {n | n ∈ d.monoid ∧ n ≠ 0}
      add_mem' := by
        rintro n m ⟨hn, hne⟩ ⟨hm, hme⟩
        refine ⟨d.monoid.add_mem hn hm, ?_⟩
        have hp : 0 < d.degree (n + m) := by
          simpa only [map_add] using add_pos (d.degree_pos hn hne) (d.degree_pos hm hme)
        intro h
        simp [h] at hp }

/-- Positive support is exactly the vanishing of coefficients at zero and outside
of the chosen monoid. -/
@[simp]
theorem mem_positiveLieAlgebra_iff (x : SkewLieAlgebra β hβ) :
    x ∈ positiveLieAlgebra β hβ d ↔
      ∀ n, n ∉ d.monoid ∨ n = 0 → toFinsupp β hβ x n = 0 := by
  classical
  rw [positiveLieAlgebra, mem_supportedLieSubalgebra_iff]
  simp only [decompose_grade, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, not_and_or,
    not_not]
  simp only [single_eq_zero]

/-- Positive support is preserved by homogeneous projection. -/
theorem positiveLieAlgebra_isHomogeneous [DecidableEq Γ] :
    DirectSum.SetLike.IsHomogeneous (grade β hβ) (positiveLieAlgebra β hβ d) := by
  unfold positiveLieAlgebra
  exact supportedLieSubalgebra_isHomogeneous (grade β hβ) _

/-- The positive skew algebra inherits the exponent pieces by inclusion. -/
def positiveGrading (n : Γ) : Submodule R (positiveLieAlgebra β hβ d) :=
  (grade β hβ n).comap (positiveLieAlgebra β hβ d).incl.toLinearMap

/-- The positive pieces are the preimages of the ambient exponent pieces. -/
theorem positiveGrading_def : positiveGrading β hβ d = fun n =>
    (grade β hβ n).comap (positiveLieAlgebra β hβ d).incl.toLinearMap := (rfl)

/-- Homogeneous membership in the positive skew algebra is ambient homogeneous membership. -/
@[simp]
theorem mem_positiveGrading_iff (n : Γ) (x : positiveLieAlgebra β hβ d) :
    x ∈ positiveGrading β hβ d n ↔ x.val ∈ grade β hβ n := Iff.rfl

instance : SetLike.GradedBracket (positiveGrading β hβ d) (positiveGrading β hβ d) := by
  rw [positiveGrading_def]
  infer_instance

/-- Restriction to positive support retains the internal direct-sum decomposition. -/
noncomputable instance [DecidableEq Γ] : GradedLieAlgebra (positiveGrading β hβ d) := by
  rw [positiveGrading_def]
  exact (positiveLieAlgebra β hβ d).gradedLieAlgebra (grade β hβ)
    (positiveLieAlgebra_isHomogeneous β hβ d)

/-- The restricted pieces vanish at zero and outside the positive monoid. -/
instance : IsPositiveGrading d (positiveGrading β hβ d) where
  eq_bot n hn := by
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨r, hr⟩ := (mem_grade_iff β hβ n x.val).mp
      ((mem_positiveGrading_iff β hβ d n x).mp hx)
    have hc := (mem_positiveLieAlgebra_iff β hβ d x.val).mp x.property n hn
    have hr0 : r = 0 := by simpa [← hr] using hc
    apply Subtype.ext
    simp [← hr, hr0]

/-- Restricting to the positive algebra preserves the abelian-ray property. -/
instance : IsAbelianRays d (positiveGrading β hβ d) := by
  apply (isAbelianRays_iff (positiveGrading β hβ d)).mpr
  intro w n m hn hm x hx y hy
  apply Subtype.ext
  exact (isAbelianRays_iff (grade β hβ)).mp inferInstance w n m hn hm
    x.val ((mem_positiveGrading_iff β hβ d n x).mp hx)
    y.val ((mem_positiveGrading_iff β hβ d m y).mp hy)

end Mei.SkewLieAlgebra
