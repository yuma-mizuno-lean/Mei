/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.Algebra.Lie.Quotient.Map
public import TauCeti.Algebra.Lie.Graded.Truncation
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

The index type here is universe-polymorphic. The upstream `truncatedLie` uses
`InternalGrading`, whose index type is in `Type 0`. For indices in `Type 0`,
`truncationIdeal_eq_degreeIdeal` identifies the ideals of the two constructions.
-/

public section

namespace TauCeti

variable {N R : Type*} [AddCommMonoid N] [CommRing R]

namespace PositiveDegrees

variable {L : Type*} [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)

variable [SetLike.GradedBracket ℒ ℒ] in
/-- Bracketing terms above cutoffs `k` and `l` gives terms above `k + l + 1`. -/
theorem bracket_mem_degreeSubmodule {k l : ℕ} {x y : L}
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
def truncationIdeal (k : ℕ) : LieIdeal R L where
  toSubmodule := d.degreeSubmodule ℒ k
  lie_mem := by
    intro x y hy
    have hx : x ∈ d.degreeSubmodule ℒ 0 := by simp
    exact d.degreeSubmodule_antitone ℒ (by omega : k ≤ 0 + k + 1)
      (d.bracket_mem_degreeSubmodule ℒ hx hy)

/-- The underlying submodule of the degree ideal is the sum of the pieces above the cutoff. -/
@[simp]
theorem truncationIdeal_toSubmodule (k : ℕ) :
    (d.truncationIdeal ℒ k).toSubmodule = d.degreeSubmodule ℒ k := (rfl)

/-- Every homogeneous piece above the cutoff lies in the degree ideal. -/
theorem le_truncationIdeal {n : N} {k : ℕ} (hn : (k : ℤ) < d.degree n) :
    ℒ n ≤ (d.truncationIdeal ℒ k).toSubmodule := by
  rw [truncationIdeal_toSubmodule]
  exact d.le_degreeSubmodule ℒ hn

/-- Degree-ideal membership is characterized by vanishing low-degree components. -/
theorem mem_truncationIdeal_iff {x : L} {k : ℕ} :
    x ∈ d.truncationIdeal ℒ k ↔
      ∀ n, d.degree n ≤ k → (DirectSum.decompose ℒ x n : L) = 0 :=
  d.mem_degreeSubmodule_iff ℒ

/-- The degree ideal is graded, using the existing homogeneous-substructure predicate. -/
theorem truncationIdeal_isGraded (k : ℕ) :
    DirectSum.SetLike.IsHomogeneous ℒ (d.truncationIdeal ℒ k) :=
  d.degreeSubmodule_isHomogeneous ℒ k

/-- Degree ideals decrease as the cutoff increases. -/
theorem truncationIdeal_antitone : Antitone (d.truncationIdeal ℒ) :=
  d.degreeSubmodule_antitone ℒ

/-- The ideal above order zero is the whole positively graded Lie algebra. -/
@[simp]
theorem truncationIdeal_zero : d.truncationIdeal ℒ 0 = ⊤ := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Brackets add filtration orders. -/
theorem lie_truncationIdeal_le (k l : ℕ) :
    ⁅d.truncationIdeal ℒ k, d.truncationIdeal ℒ l⁆ ≤ d.truncationIdeal ℒ (k + l + 1) :=
  (LieSubmodule.lie_le_iff _ _ _).mpr fun _ hx _ hy => d.bracket_mem_degreeSubmodule ℒ hx hy

/-- Mathlib's zero-based lower central series lies above the corresponding degree cutoff. -/
theorem lowerCentralSeries_le_truncationIdeal (k : ℕ) :
    LieModule.lowerCentralSeries R L L k ≤ d.truncationIdeal ℒ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LieModule.lowerCentralSeries_succ, ← d.truncationIdeal_zero ℒ]
    exact (LieSubmodule.mono_lie le_rfl ih).trans (by
      simpa using d.lie_truncationIdeal_le ℒ 0 k)

/-- The order-`k` Lie truncation, retaining homogeneous degrees at most `k`. -/
abbrev lieTruncation (k : ℕ) := L ⧸ d.truncationIdeal ℒ k

/-- The `k`-th lower central term of the order-`k` quotient vanishes. -/
theorem lowerCentralSeries_lieTruncation_eq_bot (k : ℕ) :
    LieModule.lowerCentralSeries R (d.lieTruncation ℒ k) (d.lieTruncation ℒ k) k = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq k (d.truncationIdeal ℒ k).surjective_mkQ,
    LieIdeal.map_eq_bot_iff, LieIdeal.mkQ_ker]
  exact d.lowerCentralSeries_le_truncationIdeal ℒ k

/-- Every finite degree truncation is nilpotent. -/
instance lieTruncation_isNilpotent (k : ℕ) : LieRing.IsNilpotent (d.lieTruncation ℒ k) :=
  LieModule.IsNilpotent.mk _ (d.lowerCentralSeries_lieTruncation_eq_bot ℒ k)

/-- The order-zero truncation is trivial: every degree is strictly positive. -/
instance lieTruncation_zero_subsingleton : Subsingleton (d.lieTruncation ℒ 0) :=
  subsingleton_of_forall_eq 0 fun x => by
    obtain ⟨x, rfl⟩ := (d.truncationIdeal ℒ 0).surjective_mkQ x
    exact (d.truncationIdeal ℒ 0).mkQ_eq_zero.mpr (by simp)

/-- The order-one truncation is abelian: brackets of positive degrees have
order at least two. -/
instance lieTruncation_one_isLieAbelian : IsLieAbelian (d.lieTruncation ℒ 1) :=
  (LieModule.trivial_iff_lower_central_eq_bot R _ _).mpr
    (d.lowerCentralSeries_lieTruncation_eq_bot ℒ 1)

/-- The degree-`n` piece of the truncation is the image of the original degree-`n` piece. -/
def lieTruncationGrading (k : ℕ) (n : N) : Submodule R (d.lieTruncation ℒ k) :=
  (ℒ n).map (d.truncationIdeal ℒ k).toSubmodule.mkQ

/-- Each truncated homogeneous piece is the image of the original piece. -/
@[simp]
theorem lieTruncationGrading_eq (k : ℕ) (n : N) :
    d.lieTruncationGrading ℒ k n = (ℒ n).map (d.truncationIdeal ℒ k).toSubmodule.mkQ := (rfl)

/-- An element of the truncation has degree `n` exactly when it has a representative of degree `n`.
-/
theorem mem_lieTruncationGrading_iff {k : ℕ} {n : N} {y : d.lieTruncation ℒ k} :
    y ∈ d.lieTruncationGrading ℒ k n ↔ ∃ x ∈ ℒ n, (d.truncationIdeal ℒ k).mkQ x = y := by
  rw [lieTruncationGrading_eq]
  exact Submodule.mem_map

/-- The quotient's homogeneous decomposition respects the Lie bracket. -/
noncomputable instance instGradedLieAlgebraLieTruncationGrading (k : ℕ) :
    GradedLieAlgebra (d.lieTruncationGrading ℒ k) where
  toDecomposition := by
    rw [funext (d.lieTruncationGrading_eq ℒ k)]
    apply DirectSum.IsInternal.chooseDecomposition
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · apply (DirectSum.Decomposition.isInternal ℒ).submodule_iSupIndep.map_of_ker_inf_iSup_le
      rw [Submodule.ker_mkQ]
      intro x hx
      classical
      rw [← DirectSum.sum_support_decompose ℒ x]
      exact Submodule.sum_mem _ fun n _ => Submodule.mem_iSup_of_mem n
        ⟨d.truncationIdeal_isGraded ℒ k n hx.1, (DirectSum.decompose ℒ x n).property⟩
    · simp only [← Submodule.map_iSup,
        (DirectSum.Decomposition.isInternal ℒ).submodule_iSup_eq_top,
        Submodule.map_top, Submodule.range_mkQ]
  bracket_mem := by
    intro n m x y hx hy
    obtain ⟨x, hx', rfl⟩ := (d.mem_lieTruncationGrading_iff ℒ).mp hx
    obtain ⟨y, hy', rfl⟩ := (d.mem_lieTruncationGrading_iff ℒ).mp hy
    exact (d.mem_lieTruncationGrading_iff ℒ).mpr
      ⟨⁅x, y⁆, SetLike.GradedBracket.bracket_mem hx' hy', LieHom.map_lie _ _ _⟩

/-- Truncating a positive grading preserves positivity. -/
instance lieTruncationGrading_isPositiveGrading (k : ℕ) :
    IsPositiveGrading d (d.lieTruncationGrading ℒ k) where
  eq_bot n hn := by
    rw [lieTruncationGrading_eq, IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n hn,
      Submodule.map_bot]

/-- Homogeneous projection in the truncation commutes with the quotient map. -/
@[simp]
theorem decompose_lieTruncationGrading_mk (k : ℕ) (n : N) (x : L) :
    (DirectSum.decompose (d.lieTruncationGrading ℒ k) (Submodule.Quotient.mk x) n :
      d.lieTruncation ℒ k) = Submodule.Quotient.mk (DirectSum.decompose ℒ x n : L) :=
  (DirectSum.map_decompose_shift ℒ (d.lieTruncationGrading ℒ k)
    (d.truncationIdeal ℒ k).mkQ.toLinearMap.toAddMonoidHom id Function.injective_id
    (fun _ x hx => (d.mem_lieTruncationGrading_iff ℒ).mpr ⟨x, hx, rfl⟩) n x).symm

/-- Pieces above the cutoff vanish in the truncation. -/
theorem lieTruncationGrading_eq_bot {k : ℕ} {n : N} (hn : (k : ℤ) < d.degree n) :
    d.lieTruncationGrading ℒ k n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (d.mem_lieTruncationGrading_iff ℒ).mp hx
  exact (d.truncationIdeal ℒ k).mkQ_eq_zero.mpr (d.le_truncationIdeal ℒ hn hy)

/-- A degree truncation has no terms above its retained cutoff. -/
@[simp]
theorem truncationIdeal_lieTruncationGrading_eq_bot {k l : ℕ} (hkl : k ≤ l) :
    d.truncationIdeal (d.lieTruncationGrading ℒ k) l = ⊥ := by
  apply LieSubmodule.toSubmodule_injective
  rw [truncationIdeal_toSubmodule, degreeSubmodule_def]
  exact iSup_eq_bot.mpr fun n =>
    d.lieTruncationGrading_eq_bot ℒ (lt_of_le_of_lt (by exact_mod_cast hkl) n.property)

/-- A nonzero piece in a truncation has nonzero allowed degree below the cutoff. -/
theorem mem_cutoff_of_lieTruncationGrading_ne_bot {k : ℕ} {n : N}
    (hn : d.lieTruncationGrading ℒ k n ≠ ⊥) : n ∈ d.cutoff k \ {0} := by
  have hp : n ∈ d.monoid ∧ n ≠ 0 := by
    by_contra h
    exact hn (IsPositiveGrading.eq_bot (d := d) (ℒ := d.lieTruncationGrading ℒ k) n (by tauto))
  refine ⟨d.mem_cutoff.mpr ⟨hp.1, ?_⟩, hp.2⟩
  exact le_of_not_gt (fun h => hn (d.lieTruncationGrading_eq_bot ℒ h))

/-- The surjective transition from a higher-order truncation to a lower-order one. -/
def lieTruncationMap {k l : ℕ} (h : k ≤ l) :
    d.lieTruncation ℒ l →ₗ⁅R⁆ d.lieTruncation ℒ k :=
  LieIdeal.factor (d.truncationIdeal_antitone ℒ h)

/-- The degree transition is the quotient transition induced by inclusion of degree ideals. -/
theorem lieTruncationMap_def {k l : ℕ} (h : k ≤ l) :
    d.lieTruncationMap ℒ h =
      LieIdeal.factor (d.truncationIdeal_antitone ℒ h) := (rfl)

/-- A truncation transition retains the same quotient representative. -/
@[simp]
theorem lieTruncationMap_mk {k l : ℕ} (h : k ≤ l) (x : L) :
    d.lieTruncationMap ℒ h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk x := by
  simp [lieTruncationMap]

/-- The transition at the same order is the identity. -/
@[simp]
theorem lieTruncationMap_refl (k : ℕ) : d.lieTruncationMap ℒ (le_refl k) = LieHom.id :=
  LieIdeal.factor_refl _

/-- Successive degree transitions compose to the direct transition. -/
@[simp]
theorem lieTruncationMap_comp {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (d.lieTruncationMap ℒ hkl).comp (d.lieTruncationMap ℒ hlm) =
      d.lieTruncationMap ℒ (hkl.trans hlm) :=
  LieIdeal.factor_comp _ _

/-- Every class at lower order lifts to a class at higher order. -/
theorem lieTruncationMap_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (d.lieTruncationMap ℒ h) :=
  LieIdeal.factor_surjective _

/-- At small degree types the universe-polymorphic Lie truncation ideal is the
same as the upstream degree ideal. -/
theorem truncationIdeal_eq_degreeIdeal {I : Type} {S A : Type*} [AddCommMonoid I]
    [CommRing S] [LieRing A] [LieAlgebra S A] (p : PositiveDegrees I)
    (𝒜 : I → Submodule S A) [DecidableEq I] [GradedLieAlgebra 𝒜]
    [IsPositiveGrading p 𝒜] (k : ℕ) : p.truncationIdeal 𝒜 k = p.degreeIdeal 𝒜 k := by
  apply LieSubmodule.toSubmodule_injective
  rw [truncationIdeal_toSubmodule, degreeIdeal_toSubmodule]

end PositiveDegrees
end TauCeti
