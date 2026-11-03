/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic

/-!
# Walls with a pure birth logarithm

`DirectedWall.HasPureBirthLog W S k` says that the label of `W` is `exp a` for a homogeneous
element `a ∈ S` of degree `n ∈ ℒ`, where `n` is an actual degree of the wall's supported ray
and the label is nontrivial in the truncation at order `l` exactly when `δ(n) ≤ l`. The set `S`
constrains the logarithm (for example to a kernel of a coefficient map), and `k` is an upper
bound for the birth order `δ(n)`.
-/

public section

noncomputable section

namespace Mei.DirectedWall

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

/-- A wall has a pure birth logarithm in `S` of order at most `k` when its label is the
exponential of an element `a ∈ S` homogeneous of an actual degree `n` of its supported ray
with `δ(n) ≤ k`, and its projection to order `l` is nontrivial exactly when `δ(n) ≤ l`. -/
def HasPureBirthLog (W : DirectedWall (d := d) h H) (S : Set L) (k : ℕ) : Prop :=
  ∃ n ∈ W.ray.rayDegrees, d.degree n ≤ k ∧ ∃ a ∈ ℒ n, a ∈ S ∧
    W.label = d.expToCompletion ℒ a ∧
    ∀ l : ℕ, CompletedGroup.projection l W.label ≠ 1 ↔ d.degree n ≤ l

/-- Unfolding `HasPureBirthLog`. -/
theorem hasPureBirthLog_def {W : DirectedWall (d := d) h H} {S : Set L} {k : ℕ} :
    W.HasPureBirthLog S k ↔ ∃ n ∈ W.ray.rayDegrees, d.degree n ≤ k ∧ ∃ a ∈ ℒ n, a ∈ S ∧
      W.label = d.expToCompletion ℒ a ∧
      ∀ l : ℕ, CompletedGroup.projection l W.label ≠ 1 ↔ d.degree n ≤ l := Iff.rfl

/-- A pure birth logarithm of order at most `k` is one of order at most `l ≥ k`. -/
theorem HasPureBirthLog.mono {W : DirectedWall (d := d) h H} {S : Set L} {k l : ℕ}
    (hW : W.HasPureBirthLog S k) (hkl : k ≤ l) : W.HasPureBirthLog S l := by
  obtain ⟨n, hn, hd, a, ha, haS, hl, hproj⟩ := hW
  exact ⟨n, hn, hd.trans (by exact_mod_cast hkl), a, ha, haS, hl, hproj⟩

end Mei.DirectedWall
