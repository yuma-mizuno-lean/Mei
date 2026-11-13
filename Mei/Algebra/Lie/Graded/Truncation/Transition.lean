/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import TauCeti.Algebra.Lie.Quotient
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

/-- Collecting pieces by sign commutes with lowering the degree cutoff. -/
theorem map_signSubalgebra_lieTruncationMap {A : Type*} [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] (θ : N →+ A) {k l : ℕ} (h : k ≤ l) (s : SignType) :
    (signSubalgebra (d.truncatedGrading ℒ l) θ s).map (d.truncationMap ℒ h) =
      signSubalgebra (d.truncatedGrading ℒ k) θ s :=
  map_signSubalgebra _ θ _ _ (d.map_truncationMap_truncatedGrading ℒ h) s

/-- Homogeneous projections commute with transitions. -/
@[simp]
theorem lieTruncationMap_decompose {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (n : N) :
    d.truncationMap ℒ h (DirectSum.decompose (d.truncatedGrading ℒ l) x n :
        d.truncatedLie ℒ l) =
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (d.truncationMap ℒ h x) n : d.truncatedLie ℒ k) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp [LieIdeal.mkQ_apply]

/-- A degree-transition kernel is stable under homogeneous projections. -/
theorem ker_lieTruncationMap_isHomogeneous {k l : ℕ} (h : k ≤ l) :
    DirectSum.SetLike.IsHomogeneous (d.truncatedGrading ℒ l)
      (d.truncationMap ℒ h).ker.toSubmodule := by
  intro n x hx
  simp only [LieSubmodule.mem_toSubmodule, LieHom.mem_ker] at hx ⊢
  simp [d.lieTruncationMap_decompose, hx]

/-- A nonzero homogeneous element killed by lowering the cutoff has degree
strictly above the lower cutoff. -/
theorem lt_degree_of_mem_ker_lieTruncationMap {k l : ℕ} (h : k ≤ l)
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

end TauCeti.PositiveDegrees
