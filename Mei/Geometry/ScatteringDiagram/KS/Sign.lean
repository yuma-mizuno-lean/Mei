/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Arrangement
public import Mei.Geometry.ScatteringDiagram.KS.Orthogonal
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Interior
public import Mei.Analysis.Convex.Intrinsic
public import Mei.Algebra.Lie.Graded.Sign.Basic

/-!
# Sign Lie algebras on bounded-degree arrangement cells

At a fixed cutoff the three sign Lie subalgebras are constant on the relative
interior of every degree-arrangement cell. Moreover, the zero-sign subalgebra at
such a point is exactly the orthogonal Lie algebra of the entire closed cell.
Consequently, pointwise sign factorizations can assign labels to cells without
depending on a chosen relative interior point, and their middle factors lie in
the required orthogonal wall-label group.

This combines `TauCeti.PositiveDegrees.arrangementComplex`,
`TauCeti.signSubalgebra`, and `Mei.orthogonalLieSubalgebra` using the relative-interior
characterization of realized sign cells. Only degrees with a nonzero piece in
the truncation matter; degrees above the cutoff impose no extra condition.
-/

public section

open TauCeti.Convex (intrinsicInterior_closure_signCell
  row_eq_zero_iff_forall_of_mem_intrinsicInterior)

open TauCeti (signSubalgebra signSubalgebra_eq_of_sign_eq mem_signSubalgebra_iff)

open TauCeti (PositiveDegrees IsPositiveGrading)

namespace TauCeti.PositiveDegrees

open Mei

open Mei.Convex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)
  {k : ℕ} {P : Set (V →L[ℝ] ℝ)}

/-- Every retained nonzero degree has constant sign on a cell's relative interior. -/
theorem sign_eq_of_mem_intrinsicInterior_arrangementComplex
    (hP : P ∈ (d.arrangementComplex h k).cells)
    {θ φ : V →L[ℝ] ℝ} (hθ : θ ∈ intrinsicInterior ℝ P)
    (hφ : φ ∈ intrinsicInterior ℝ P) {n : N} (hn : n ∈ d.cutoff k \ {0}) :
    SignType.sign (θ (i n)) = SignType.sign (φ (i n)) := by
  obtain ⟨σ, _, rfl⟩ := (d.mem_arrangementComplex_cells h k P).mp hP
  rw [intrinsicInterior_closure_signCell] at hθ hφ
  exact (TauCeti.Convex.mem_signCell.mp hθ ⟨n, hn⟩).trans
    (TauCeti.Convex.mem_signCell.mp hφ ⟨n, hn⟩).symm

/-- A retained degree annihilates a relative interior point exactly when it
annihilates the entire arrangement cell. -/
theorem eval_eq_zero_iff_forall_of_mem_intrinsicInterior_arrangementComplex
    (hP : P ∈ (d.arrangementComplex h k).cells)
    {θ : V →L[ℝ] ℝ} (hθ : θ ∈ intrinsicInterior ℝ P)
    {n : N} (hn : n ∈ d.cutoff k \ {0}) :
    θ (i n) = 0 ↔ ∀ φ ∈ P, φ (i n) = 0 := by
  obtain ⟨σ, _, rfl⟩ := (d.mem_arrangementComplex_cells h k P).mp hP
  exact row_eq_zero_iff_forall_of_mem_intrinsicInterior hθ ⟨n, hn⟩

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [DecidableEq N] (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ]

/-- The three finite sign Lie subalgebras are independent of the chosen relative
interior point of a bounded-degree arrangement cell. -/
theorem signSubalgebra_eq_of_mem_intrinsicInterior_arrangementComplex
    (hP : P ∈ (d.arrangementComplex h k).cells)
    {θ φ : V →L[ℝ] ℝ} (hθ : θ ∈ intrinsicInterior ℝ P)
    (hφ : φ ∈ intrinsicInterior ℝ P) (s : SignType) :
    signSubalgebra (d.lieTruncationGrading ℒ k) (θ.toAddMonoidHom.comp i) s =
      signSubalgebra (d.lieTruncationGrading ℒ k) (φ.toAddMonoidHom.comp i) s := by
  apply signSubalgebra_eq_of_sign_eq
  intro n hn
  exact d.sign_eq_of_mem_intrinsicInterior_arrangementComplex h hP hθ hφ
    (d.mem_cutoff_of_lieTruncationGrading_ne_bot ℒ hn)

/-- The middle sign algebra at a cell's relative interior point is precisely
the finite orthogonal algebra of the whole cell. -/
theorem signSubalgebra_zero_eq_orthogonalLieSubalgebra
    (hP : P ∈ (d.arrangementComplex h k).cells)
    {θ : V →L[ℝ] ℝ} (hθ : θ ∈ intrinsicInterior ℝ P) :
    signSubalgebra (d.lieTruncationGrading ℒ k) (θ.toAddMonoidHom.comp i) 0 =
      orthogonalLieSubalgebra (d.lieTruncationGrading ℒ k)
        ((fun φ : V →L[ℝ] ℝ => φ.toAddMonoidHom.comp i) '' P) := by
  ext x
  rw [mem_signSubalgebra_iff, mem_orthogonalLieSubalgebra_iff]
  constructor
  · intro hx ψ hψ n hψn
    obtain ⟨φ, hφ, rfl⟩ := hψ
    by_cases hn : d.lieTruncationGrading ℒ k n = ⊥
    · simpa only [hn, Submodule.mem_bot] using
        (DirectSum.decompose (d.lieTruncationGrading ℒ k) x n).property
    · apply hx n
      intro hn0
      have hθn : θ (i n) = 0 := sign_eq_zero_iff.mp hn0
      exact hψn ((d.eval_eq_zero_iff_forall_of_mem_intrinsicInterior_arrangementComplex
        h hP hθ (d.mem_cutoff_of_lieTruncationGrading_ne_bot ℒ hn)).mp hθn φ hφ)
  · intro hx n hn
    exact hx _ ⟨θ, intrinsicInterior_subset hθ, rfl⟩ n
      (fun hn0 => hn (sign_eq_zero_iff.mpr hn0))

end TauCeti.PositiveDegrees
