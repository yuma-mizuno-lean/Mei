/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.Algebra.Lie.Quotient.Map
public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Algebra.Lie.Nilpotent

/-!
# Degree ideals and nilpotent truncations

For a positively graded Lie algebra, the sum of the homogeneous pieces above a
degree cutoff is a homogeneous Lie ideal. Bracketing adds degrees, so the lower
central series lies in these ideals and every degree truncation is nilpotent.

The construction uses Mathlib's `GradedLieAlgebra` and `SetLike.IsHomogeneous` on
the original homogeneous submodules. No freeness, finite rank, or assumption on
the coefficient ring beyond commutativity is needed.

The quotient decomposition follows `TauCeti.InternalGrading.quotient`, using
`iSupIndep.map_of_ker_inf_iSup_le` to preserve independence under the quotient
map. It keeps the images of the original pieces as submodules of the quotient.
The natural surjective transitions between cutoffs use `LieIdeal.factor`.
-/

public section

namespace Mei

variable {N R : Type*} [AddCommMonoid N] [CommRing R]

namespace PositiveDegrees

variable {L : Type*} [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)

variable [SetLike.GradedBracket ℒ ℒ] in
/-- Bracketing terms above cutoffs `k` and `l` gives terms above `k + l + 1`. -/
theorem lie_mem_degreeSubmodule {k l : ℕ} {x y : L}
    (hx : x ∈ d.degreeSubmodule ℒ k) (hy : y ∈ d.degreeSubmodule ℒ l) :
    ⁅x, y⁆ ∈ d.degreeSubmodule ℒ (k + l + 1) := by
  rw [degreeSubmodule_def] at hx hy
  refine Submodule.iSup_induction _ (motive := fun x =>
    ⁅x, y⁆ ∈ d.degreeSubmodule ℒ (k + l + 1)) hx
    (fun n x hx => ?_) ?_ (fun x z hx hz => ?_)
  · refine Submodule.iSup_induction _ (motive := fun y =>
      ⁅x, y⁆ ∈ d.degreeSubmodule ℒ (k + l + 1)) hy
      (fun m y hy => ?_) ?_ (fun y z hy hz => ?_)
    · apply d.le_degreeSubmodule ℒ (n := n.val + m.val)
        (by rw [map_add]; have := n.property; have := m.property; omega)
      simpa only [vadd_eq_add] using SetLike.GradedBracket.bracket_mem hx hy
    · simp
    · simpa [lie_add] using Submodule.add_mem _ hy hz
  · simp
  · simpa [add_lie] using Submodule.add_mem _ hx hz

variable [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The homogeneous Lie ideal of terms above order `k`, also denoted `F^{k+1}`. -/
def degreeIdeal (k : ℕ) : LieIdeal R L where
  toSubmodule := d.degreeSubmodule ℒ k
  lie_mem := by
    intro x y hy
    have hx : x ∈ d.degreeSubmodule ℒ 0 := by simp
    exact d.degreeSubmodule_antitone ℒ (by omega : k ≤ 0 + k + 1)
      (d.lie_mem_degreeSubmodule ℒ hx hy)

/-- The underlying submodule of the degree ideal is the sum of the pieces above the cutoff. -/
@[simp]
theorem degreeIdeal_toSubmodule (k : ℕ) :
    (d.degreeIdeal ℒ k).toSubmodule = d.degreeSubmodule ℒ k := (rfl)

/-- Every homogeneous piece above the cutoff lies in the degree ideal. -/
theorem le_degreeIdeal {n : N} {k : ℕ} (hn : (k : ℤ) < d.degree n) :
    ℒ n ≤ (d.degreeIdeal ℒ k).toSubmodule := by
  rw [degreeIdeal_toSubmodule]
  exact d.le_degreeSubmodule ℒ hn

/-- Degree-ideal membership is characterized by vanishing low-degree components. -/
theorem mem_degreeIdeal_iff {x : L} {k : ℕ} :
    x ∈ d.degreeIdeal ℒ k ↔
      ∀ n, d.degree n ≤ k → (DirectSum.decompose ℒ x n : L) = 0 :=
  d.mem_degreeSubmodule_iff ℒ

/-- The degree ideal is graded, using the existing homogeneous-substructure predicate. -/
theorem degreeIdeal_isGraded (k : ℕ) :
    DirectSum.SetLike.IsHomogeneous ℒ (d.degreeIdeal ℒ k) :=
  d.degreeSubmodule_isHomogeneous ℒ k

/-- Degree ideals decrease as the cutoff increases. -/
theorem degreeIdeal_antitone : Antitone (d.degreeIdeal ℒ) :=
  d.degreeSubmodule_antitone ℒ

/-- The ideal above order zero is the whole positively graded Lie algebra. -/
@[simp]
theorem degreeIdeal_zero : d.degreeIdeal ℒ 0 = ⊤ := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Brackets add filtration orders. -/
theorem lie_degreeIdeal_le (k l : ℕ) :
    ⁅d.degreeIdeal ℒ k, d.degreeIdeal ℒ l⁆ ≤ d.degreeIdeal ℒ (k + l + 1) :=
  (LieSubmodule.lie_le_iff _ _ _).mpr fun _ hx _ hy => d.lie_mem_degreeSubmodule ℒ hx hy

/-- Mathlib's zero-based lower central series lies above the corresponding degree cutoff. -/
theorem lowerCentralSeries_le_degreeIdeal (k : ℕ) :
    LieModule.lowerCentralSeries R L L k ≤ d.degreeIdeal ℒ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LieModule.lowerCentralSeries_succ, ← d.degreeIdeal_zero ℒ]
    exact (LieSubmodule.mono_lie le_rfl ih).trans (by
      simpa using d.lie_degreeIdeal_le ℒ 0 k)

/-- The order-`k` Lie truncation, retaining homogeneous degrees at most `k`. -/
abbrev truncatedLie (k : ℕ) := L ⧸ d.degreeIdeal ℒ k

/-- The `k`-th lower central term of the order-`k` quotient vanishes. -/
theorem lowerCentralSeries_truncatedLie_eq_bot (k : ℕ) :
    LieModule.lowerCentralSeries R (d.truncatedLie ℒ k) (d.truncatedLie ℒ k) k = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq k (d.degreeIdeal ℒ k).surjective_mkQ,
    LieIdeal.map_eq_bot_iff, LieIdeal.mkQ_ker]
  exact d.lowerCentralSeries_le_degreeIdeal ℒ k

/-- Every finite degree truncation is nilpotent. -/
instance truncatedLie_isNilpotent (k : ℕ) : LieRing.IsNilpotent (d.truncatedLie ℒ k) :=
  LieModule.IsNilpotent.mk _ (d.lowerCentralSeries_truncatedLie_eq_bot ℒ k)

/-- The degree-`n` piece of the truncation is the image of the original degree-`n` piece. -/
def truncatedGrading (k : ℕ) (n : N) : Submodule R (d.truncatedLie ℒ k) :=
  (ℒ n).map (d.degreeIdeal ℒ k).toSubmodule.mkQ

/-- Each truncated homogeneous piece is the image of the original piece. -/
@[simp]
theorem truncatedGrading_eq (k : ℕ) (n : N) :
    d.truncatedGrading ℒ k n = (ℒ n).map (d.degreeIdeal ℒ k).toSubmodule.mkQ := (rfl)

/-- An element of the truncation has degree `n` exactly when it has a representative of degree `n`.
-/
theorem mem_truncatedGrading_iff {k : ℕ} {n : N} {y : d.truncatedLie ℒ k} :
    y ∈ d.truncatedGrading ℒ k n ↔ ∃ x ∈ ℒ n, (d.degreeIdeal ℒ k).mkQ x = y := by
  rw [truncatedGrading_eq]
  exact Submodule.mem_map

/-- The quotient's homogeneous decomposition respects the Lie bracket. -/
noncomputable instance instGradedLieAlgebraTruncatedGrading (k : ℕ) :
    GradedLieAlgebra (d.truncatedGrading ℒ k) where
  toDecomposition := by
    rw [funext (d.truncatedGrading_eq ℒ k)]
    apply DirectSum.IsInternal.chooseDecomposition
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · apply (DirectSum.Decomposition.isInternal ℒ).submodule_iSupIndep.map_of_ker_inf_iSup_le
      rw [Submodule.ker_mkQ]
      intro x hx
      classical
      rw [← DirectSum.sum_support_decompose ℒ x]
      exact Submodule.sum_mem _ fun n _ => Submodule.mem_iSup_of_mem n
        ⟨d.degreeIdeal_isGraded ℒ k n hx.1, (DirectSum.decompose ℒ x n).property⟩
    · simp only [← Submodule.map_iSup,
        (DirectSum.Decomposition.isInternal ℒ).submodule_iSup_eq_top,
        Submodule.map_top, Submodule.range_mkQ]
  bracket_mem := by
    intro n m x y hx hy
    obtain ⟨x, hx', rfl⟩ := (d.mem_truncatedGrading_iff ℒ).mp hx
    obtain ⟨y, hy', rfl⟩ := (d.mem_truncatedGrading_iff ℒ).mp hy
    exact (d.mem_truncatedGrading_iff ℒ).mpr
      ⟨⁅x, y⁆, SetLike.GradedBracket.bracket_mem hx' hy', LieHom.map_lie _ _ _⟩

/-- Truncating a positive grading preserves positivity. -/
instance truncatedGrading_isPositiveGrading (k : ℕ) :
    IsPositiveGrading d (d.truncatedGrading ℒ k) where
  eq_bot n hn := by
    rw [truncatedGrading_eq, IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n hn,
      Submodule.map_bot]

/-- Homogeneous projection in the truncation commutes with the quotient map. -/
@[simp]
theorem decompose_truncatedGrading_mk (k : ℕ) (n : N) (x : L) :
    (DirectSum.decompose (d.truncatedGrading ℒ k) (Submodule.Quotient.mk x) n :
      d.truncatedLie ℒ k) = Submodule.Quotient.mk (DirectSum.decompose ℒ x n : L) :=
  (DirectSum.map_decompose_shift ℒ (d.truncatedGrading ℒ k)
    (d.degreeIdeal ℒ k).mkQ.toLinearMap.toAddMonoidHom id Function.injective_id
    (fun _ x hx => (d.mem_truncatedGrading_iff ℒ).mpr ⟨x, hx, rfl⟩) n x).symm

/-- Pieces above the cutoff vanish in the truncation. -/
theorem truncatedGrading_eq_bot {k : ℕ} {n : N} (hn : (k : ℤ) < d.degree n) :
    d.truncatedGrading ℒ k n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (d.mem_truncatedGrading_iff ℒ).mp hx
  exact (d.degreeIdeal ℒ k).mkQ_eq_zero.mpr (d.le_degreeIdeal ℒ hn hy)

/-- The surjective transition from a higher-order truncation to a lower-order one. -/
def truncationMap {k l : ℕ} (h : k ≤ l) :
    d.truncatedLie ℒ l →ₗ⁅R⁆ d.truncatedLie ℒ k :=
  (d.degreeIdeal ℒ l).factor (d.degreeIdeal ℒ k) (d.degreeIdeal_antitone ℒ h)

/-- A truncation transition retains the same quotient representative. -/
@[simp]
theorem truncationMap_mk {k l : ℕ} (h : k ≤ l) (x : L) :
    d.truncationMap ℒ h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk x := by
  simp [truncationMap]

/-- The transition at the same order is the identity. -/
@[simp]
theorem truncationMap_refl (k : ℕ) : d.truncationMap ℒ (le_refl k) = LieHom.id :=
  LieIdeal.factor_refl _

/-- Successive degree transitions compose to the direct transition. -/
@[simp]
theorem truncationMap_comp {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (d.truncationMap ℒ hkl).comp (d.truncationMap ℒ hlm) =
      d.truncationMap ℒ (hkl.trans hlm) :=
  LieIdeal.factor_comp _ _ _ _ _

/-- Every class at lower order lifts to a class at higher order. -/
theorem truncationMap_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (d.truncationMap ℒ h) :=
  LieIdeal.factor_surjective _ _ _

end PositiveDegrees
end Mei
