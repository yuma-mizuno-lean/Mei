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

open TauCeti (signSubalgebra map_signSubalgebra)

namespace TauCeti.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : TauCeti.PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- A transition maps each homogeneous piece onto the corresponding piece. -/
theorem map_lieTruncationGrading_lieTruncationMap {k l : ℕ} (h : k ≤ l) (n : N) :
    (d.lieTruncationGrading ℒ l n).map (d.lieTruncationMap ℒ h).toLinearMap =
      d.lieTruncationGrading ℒ k n := by
  rw [lieTruncationMap_def, lieTruncationGrading_eq, ← Submodule.map_comp, lieTruncationGrading_eq]
  congr 1
  ext x
  exact LieIdeal.factor_apply _ x

/-- Collecting pieces by sign commutes with lowering the degree cutoff. -/
theorem map_signSubalgebra_lieTruncationMap {A : Type*} [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] (θ : N →+ A) {k l : ℕ} (h : k ≤ l) (s : SignType) :
    (signSubalgebra (d.lieTruncationGrading ℒ l) θ s).map (d.lieTruncationMap ℒ h) =
      signSubalgebra (d.lieTruncationGrading ℒ k) θ s :=
  map_signSubalgebra _ θ _ _ (d.map_lieTruncationGrading_lieTruncationMap ℒ h) s

/-- Homogeneous projections commute with transitions. -/
@[simp]
theorem lieTruncationMap_decompose {k l : ℕ} (h : k ≤ l)
    (x : d.lieTruncation ℒ l) (n : N) :
    d.lieTruncationMap ℒ h (DirectSum.decompose (d.lieTruncationGrading ℒ l) x n :
        d.lieTruncation ℒ l) =
      (DirectSum.decompose (d.lieTruncationGrading ℒ k)
        (d.lieTruncationMap ℒ h x) n : d.lieTruncation ℒ k) := by
  obtain ⟨x, rfl⟩ := (d.truncationIdeal ℒ l).surjective_mkQ x
  simp [LieIdeal.mkQ_apply]

/-- A degree-transition kernel is stable under homogeneous projections. -/
theorem ker_lieTruncationMap_isHomogeneous {k l : ℕ} (h : k ≤ l) :
    DirectSum.SetLike.IsHomogeneous (d.lieTruncationGrading ℒ l)
      (d.lieTruncationMap ℒ h).ker.toSubmodule := by
  intro n x hx
  simp only [LieSubmodule.mem_toSubmodule, LieHom.mem_ker] at hx ⊢
  simp [d.lieTruncationMap_decompose, hx]

/-- A nonzero homogeneous element killed by lowering the cutoff has degree
strictly above the lower cutoff. -/
theorem lt_degree_of_mem_ker_lieTruncationMap {k l : ℕ} (h : k ≤ l)
    {n : N} {x : d.lieTruncation ℒ l} (hx : x ∈ d.lieTruncationGrading ℒ l n)
    (hker : x ∈ (d.lieTruncationMap ℒ h).ker) (hne : x ≠ 0) :
    (k : ℤ) < d.degree n := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_lieTruncationGrading_iff ℒ).mp hx
  have hzero : (d.truncationIdeal ℒ k).mkQ a = 0 := by
    simpa only [LieHom.mem_ker, LieIdeal.mkQ_apply, d.lieTruncationMap_mk] using hker
  have hmem : a ∈ d.degreeSubmodule ℒ k := by
    simpa only [← LieSubmodule.mem_toSubmodule, truncationIdeal_toSubmodule] using
      (d.truncationIdeal ℒ k).mkQ_eq_zero.mp hzero
  exact ((d.mem_degreeSubmodule_of_mem_iff ℒ ha).mp hmem).resolve_left
    (fun he => hne (by simp [he]))

/-- Only the degrees in `(k, l]` survive in the kernel from order `l` to order `k`. -/
theorem ker_lieTruncationMap_eq_iSup {k l : ℕ} (h : k ≤ l) :
    (d.lieTruncationMap ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n ∧ d.degree n ≤ l},
        d.lieTruncationGrading ℒ l n := by
  have hpieces : (d.lieTruncationMap ℒ h).ker.toSubmodule =
      ⨆ n : {n : N // (k : ℤ) < d.degree n}, d.lieTruncationGrading ℒ l n := by
    rw [lieTruncationMap_def, LieIdeal.ker_factor,
      LieIdeal.coe_map_of_surjective (d.truncationIdeal ℒ l).surjective_mkQ,
      truncationIdeal_toSubmodule, degreeSubmodule_def, Submodule.map_iSup]
    congr 1
    funext n
    rw [lieTruncationGrading_eq]
    -- The Lie quotient projection has the underlying module quotient projection.
    rfl
  rw [hpieces]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    by_cases hn : d.degree n ≤ l
    · exact le_iSup_of_le ⟨n, n.property, hn⟩ le_rfl
    · rw [d.lieTruncationGrading_eq_bot ℒ (lt_of_not_ge hn)]
      exact bot_le
  · exact iSup_le fun n => le_iSup_of_le ⟨n, n.property.1⟩ le_rfl

/-- A successive kernel is exactly the sum of the pieces of the newly retained degree. -/
theorem ker_lieTruncationMap_succ (k : ℕ) :
    (d.lieTruncationMap ℒ (Nat.le_succ k)).ker.toSubmodule =
      ⨆ n : {n : N // d.degree n = (k : ℤ) + 1},
        d.lieTruncationGrading ℒ (k + 1) n := by
  rw [ker_lieTruncationMap_eq_iSup]
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
theorem ker_lieTruncationMap_succ_le_center (k : ℕ) :
    (d.lieTruncationMap ℒ (Nat.le_succ k)).ker ≤
      LieAlgebra.center R (d.lieTruncation ℒ (k + 1)) := by
  rw [lieTruncationMap_def]
  apply (LieIdeal.ker_factor_le_center_iff _ _ _).mpr
  rw [← d.truncationIdeal_zero ℒ]
  simpa using d.lie_truncationIdeal_le ℒ 0 k

/-- The kernel of a successive truncation is abelian. -/
instance isLieAbelian_ker_lieTruncationMap_succ (k : ℕ) :
    IsLieAbelian (d.lieTruncationMap ℒ (Nat.le_succ k)).ker :=
  LieAlgebra.abelian_of_le_center R _ _ (d.ker_lieTruncationMap_succ_le_center ℒ k)

end TauCeti.PositiveDegrees
