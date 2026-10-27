/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import Mei.Algebra.Lie.Quotient.Map
public import Mei.Algebra.Lie.Graded.Sign.Basic

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

/-- A transition maps each homogeneous piece onto the corresponding piece. -/
theorem map_truncatedGrading_truncationMap {k l : ℕ} (h : k ≤ l) (n : N) :
    (d.truncatedGrading ℒ l n).map (d.truncationMap ℒ h).toLinearMap =
      d.truncatedGrading ℒ k n := by
  rw [truncationMap_def, truncatedGrading_eq, ← Submodule.map_comp, truncatedGrading_eq]
  congr 1
  ext x
  exact LieIdeal.factor_apply _ _ _ x

/-- Collecting pieces by sign commutes with lowering the degree cutoff. -/
theorem map_signSubalgebra_truncationMap {A : Type*} [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] (θ : N →+ A) {k l : ℕ} (h : k ≤ l) (s : SignType) :
    (signSubalgebra (d.truncatedGrading ℒ l) θ s).map (d.truncationMap ℒ h) =
      signSubalgebra (d.truncatedGrading ℒ k) θ s :=
  map_signSubalgebra _ θ _ _ (d.map_truncatedGrading_truncationMap ℒ h) s

/-- Homogeneous projections commute with transitions. -/
@[simp]
theorem truncationMap_decompose {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (n : N) :
    d.truncationMap ℒ h (DirectSum.decompose (d.truncatedGrading ℒ l) x n :
        d.truncatedLie ℒ l) =
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (d.truncationMap ℒ h x) n : d.truncatedLie ℒ k) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp [LieIdeal.mkQ_apply]

/-- A degree-transition kernel is stable under homogeneous projections. -/
theorem ker_truncationMap_isHomogeneous {k l : ℕ} (h : k ≤ l) :
    DirectSum.SetLike.IsHomogeneous (d.truncatedGrading ℒ l)
      (d.truncationMap ℒ h).ker.toSubmodule := by
  intro n x hx
  simp only [LieSubmodule.mem_toSubmodule, LieHom.mem_ker] at hx ⊢
  simp [d.truncationMap_decompose, hx]

/-- A nonzero homogeneous element killed by lowering the cutoff has degree
strictly above the lower cutoff. -/
theorem lt_degree_of_mem_ker_truncationMap {k l : ℕ} (h : k ≤ l)
    {n : N} {x : d.truncatedLie ℒ l} (hx : x ∈ d.truncatedGrading ℒ l n)
    (hker : x ∈ (d.truncationMap ℒ h).ker) (hne : x ≠ 0) :
    (k : ℤ) < d.degree n := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_truncatedGrading_iff ℒ).mp hx
  have hzero : (d.degreeIdeal ℒ k).mkQ a = 0 := by
    simpa only [LieHom.mem_ker, LieIdeal.mkQ_apply, d.truncationMap_mk] using hker
  have hmem : a ∈ d.degreeSubmodule ℒ k := by
    simpa only [← LieSubmodule.mem_toSubmodule, degreeIdeal_toSubmodule] using
      (d.degreeIdeal ℒ k).mkQ_eq_zero.mp hzero
  exact ((d.mem_degreeSubmodule_of_mem_iff ℒ ha).mp hmem).resolve_left
    (fun he => hne (by simp [he]))

/-- Only the degrees in `(k, l]` survive in the kernel from order `l` to order `k`. -/
theorem ker_truncationMap_eq_iSup {k l : ℕ} (h : k ≤ l) :
    (d.truncationMap ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n ∧ d.degree n ≤ l},
        d.truncatedGrading ℒ l n := by
  have hpieces : (d.truncationMap ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n}, d.truncatedGrading ℒ l n := by
    rw [truncationMap_def, LieIdeal.ker_factor,
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
theorem ker_truncationMap_succ (k : ℕ) :
    (d.truncationMap ℒ (Nat.le_succ k)).ker.toSubmodule =
      ⨆ n : {n : N // d.degree n = (k : ℤ) + 1},
        d.truncatedGrading ℒ (k + 1) n := by
  rw [ker_truncationMap_eq_iSup]
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
theorem ker_truncationMap_succ_le_center (k : ℕ) :
    (d.truncationMap ℒ (Nat.le_succ k)).ker ≤
      LieAlgebra.center R (d.truncatedLie ℒ (k + 1)) := by
  rw [truncationMap_def]
  apply (LieIdeal.ker_factor_le_center_iff _ _ _).mpr
  rw [← d.degreeIdeal_zero ℒ]
  simpa using d.lie_degreeIdeal_le ℒ 0 k

/-- The kernel of a successive truncation is abelian. -/
instance isLieAbelian_ker_truncationMap_succ (k : ℕ) :
    IsLieAbelian (d.truncationMap ℒ (Nat.le_succ k)).ker :=
  LieAlgebra.abelian_of_le_center R _ _ (d.ker_truncationMap_succ_le_center ℒ k)

end Mei.PositiveDegrees
