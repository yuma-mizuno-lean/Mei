/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import Mei.Algebra.Lie.Quotient.Map

/-!
# Transitions between Lie algebra truncations

The finite degree truncations of a positively graded Lie algebra form a
surjective tower. Its transitions preserve homogeneous pieces and commute with
homogeneous projections. The kernel from order `l` to order `k` is the sum of
the surviving pieces with degrees in `(k, l]`.

In particular, the transition from order `k + 1` to order `k` has central kernel,
equal to the image of the pieces of degree exactly `k + 1`. This describes each
stage of the tower as a central extension, allowing constructions by induction
on the degree cutoff.

The transitions use `LieIdeal.factor`, and the kernel and centrality arguments
specialize its general quotient API.
-/

public section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : Mei.PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [Mei.IsPositiveGrading d ℒ]

/-- The canonical transition from a finer degree truncation to a coarser one. -/
def truncationTransition {k l : ℕ} (h : k ≤ l) :
    d.truncatedLie ℒ l →ₗ⁅R⁆ d.truncatedLie ℒ k :=
  (d.degreeIdeal ℒ l).factor (d.degreeIdeal ℒ k) (d.degreeIdeal_antitone ℒ h)

/-- A transition preserves the representative of a quotient class. -/
@[simp]
theorem truncationTransition_mk {k l : ℕ} (h : k ≤ l) (x : L) :
    d.truncationTransition ℒ h (LieSubmodule.Quotient.mk x) =
      LieSubmodule.Quotient.mk x :=
  LieIdeal.factor_apply _ _ _ _

/-- The transition at a fixed cutoff is the identity. -/
@[simp]
theorem truncationTransition_refl (k : ℕ) :
    d.truncationTransition ℒ (le_refl k) = LieHom.id :=
  LieIdeal.factor_refl _

/-- Successive transitions agree with the direct transition. -/
@[simp]
theorem truncationTransition_comp {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (d.truncationTransition ℒ hkl).comp (d.truncationTransition ℒ hlm) =
      d.truncationTransition ℒ (hkl.trans hlm) :=
  LieIdeal.factor_comp _ _ _ _ _

/-- Every class at a coarser cutoff lifts to any finer cutoff. -/
theorem truncationTransition_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (d.truncationTransition ℒ h) :=
  LieIdeal.factor_surjective _ _ _

/-- A transition maps each homogeneous piece onto the corresponding piece. -/
theorem map_truncatedGrading_truncationTransition {k l : ℕ} (h : k ≤ l) (n : N) :
    (d.truncatedGrading ℒ l n).map (d.truncationTransition ℒ h).toLinearMap =
      d.truncatedGrading ℒ k n := by
  rw [truncatedGrading_eq, ← Submodule.map_comp, truncatedGrading_eq]
  congr 1
  ext x
  exact d.truncationTransition_mk ℒ h x

/-- Homogeneous projections commute with transitions. -/
@[simp]
theorem truncationTransition_decompose {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (n : N) :
    d.truncationTransition ℒ h (DirectSum.decompose (d.truncatedGrading ℒ l) x n :
        d.truncatedLie ℒ l) =
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (d.truncationTransition ℒ h x) n : d.truncatedLie ℒ k) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp [LieIdeal.mkQ_apply]

/-- The transition kernel is the image of the coarser cutoff ideal. -/
theorem ker_truncationTransition {k l : ℕ} (h : k ≤ l) :
    (d.truncationTransition ℒ h).ker =
      (d.degreeIdeal ℒ k).map (d.degreeIdeal ℒ l).mkQ :=
  LieIdeal.ker_factor _ _ _

/-- Only the degrees in `(k, l]` survive in the kernel from order `l` to order `k`. -/
theorem ker_truncationTransition_eq_iSup {k l : ℕ} (h : k ≤ l) :
    (d.truncationTransition ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n ∧ d.degree n ≤ l},
        d.truncatedGrading ℒ l n := by
  have hpieces : (d.truncationTransition ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n}, d.truncatedGrading ℒ l n := by
    rw [ker_truncationTransition,
      LieIdeal.coe_map_of_surjective (d.degreeIdeal ℒ l).surjective_mkQ,
      degreeIdeal_toSubmodule, degreeSubmodule_def, Submodule.map_iSup]
    congr 1
    funext n
    rw [truncatedGrading_eq]
    -- The Lie quotient projection has the underlying module quotient projection.
    rfl
  rw [hpieces]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    by_cases hn : d.degree n ≤ l
    · exact le_iSup_of_le ⟨n, n.property, hn⟩ le_rfl
    · rw [d.truncatedGrading_eq_bot ℒ (lt_of_not_ge hn)]
      exact bot_le
  · exact iSup_le fun n => le_iSup_of_le ⟨n, n.property.1⟩ le_rfl

/-- A successive kernel is exactly the sum of the pieces of the newly retained degree. -/
theorem ker_truncationTransition_succ (k : ℕ) :
    (d.truncationTransition ℒ (Nat.le_succ k)).ker.toSubmodule =
      ⨆ n : {n : N // d.degree n = (k : ℤ) + 1},
        d.truncatedGrading ℒ (k + 1) n := by
  rw [ker_truncationTransition_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun n => le_iSup_of_le ⟨n, ?_⟩ le_rfl
    have := n.property
    push_cast at this
    omega
  · refine iSup_le fun n => le_iSup_of_le ⟨n, ?_⟩ le_rfl
    have := n.property
    constructor <;> omega

/-- Successive truncations are central extensions: bracketing their kernel with
any element of the finer truncation gives zero. -/
theorem ker_truncationTransition_succ_le_center (k : ℕ) :
    (d.truncationTransition ℒ (Nat.le_succ k)).ker ≤
      LieAlgebra.center R (d.truncatedLie ℒ (k + 1)) := by
  apply (LieIdeal.ker_factor_le_center_iff _ _ _).mpr
  rw [← d.degreeIdeal_zero ℒ]
  simpa using d.lie_degreeIdeal_le ℒ 0 k

end Mei.PositiveDegrees
