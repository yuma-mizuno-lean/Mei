/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction

/-!
# Assembling directed correction families

Assemble indexed wall families born at successive orders into a single directed
diagram. Each family need only be finitely active at every cutoff; the family born
at order `n` must be invisible below `n`. The zeroth family can therefore be an
arbitrary initial diagram. At order `k`, only the first `k + 1` families contribute.
If these bounded stages are consistent at their respective orders, the assembled
diagram is consistent at every order and has the existing completed transport.

This is the passage from compatible finite-order corrections to an all-order wall
family. It uses finite unions of the individual active sets and
`DirectedDiagram.levelEquivalent_restrict`; it does not require the supports to
stabilize or the union of all walls to be locally finite.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V : Type*} {ι : ℕ → Type*}
  [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : ∀ n, DirectedDiagram (d := d) h H (ι n))
  (hbirth : ∀ n k, k < n → ∀ j, CompletedGroup.projection k ((D n).wall j).label = 1)

/-- The union of successive wall families whose birth orders tend to infinity.
Indices remember their birth family, so repeated walls are retained separately. -/
def ofBirthFamily : DirectedDiagram (d := d) h H (Σ n, ι n) where
  wall j := (D j.1).wall j.2
  finite_active k := by
    have hfinite : (⋃ n ∈ Iic k, Sigma.mk n '' (D n).active k).Finite :=
      (finite_Iic k).biUnion fun n _ => (Set.toFinite ((D n).active k)).image (Sigma.mk n)
    apply hfinite.subset
    intro j hj
    have hle : j.1 ≤ k := by
      by_contra hn
      exact hj (hbirth j.1 k (by omega) j.2)
    exact mem_iUnion₂.mpr ⟨j.1, hle,
      mem_image_of_mem _ (((D j.1).mem_active k j.2).mpr hj)⟩

@[simp]
theorem ofBirthFamily_wall (j : Σ n, ι n) :
    (ofBirthFamily D hbirth).wall j = (D j.1).wall j.2 := (rfl)

/-- An active wall of the assembled diagram has already been born. -/
theorem birth_le_of_mem_active {k : ℕ} {j : Σ n, ι n}
    (hj : j ∈ (ofBirthFamily D hbirth).active k) : j.1 ≤ k := by
  by_contra hn
  have hne : CompletedGroup.projection k ((D j.1).wall j.2).label ≠ 1 := by
    simpa only [mem_active, ofBirthFamily_wall] using hj
  exact hne (hbirth j.1 k (by omega) j.2)

/-- Any bounded stage containing the first `k + 1` birth families computes all
order-`k` products of the assembled diagram on common admissible paths. -/
theorem ofBirthFamily_levelEquivalent_restrict {k m : ℕ} (hkm : k ≤ m) :
    (ofBirthFamily D hbirth).LevelEquivalent
      ((ofBirthFamily D hbirth).restrict {j | j.1 ≤ m}) k :=
  (ofBirthFamily D hbirth).levelEquivalent_restrict fun _ hj =>
    (birth_le_of_mem_active D hbirth hj).trans hkm

/-- The assembled diagram is consistent exactly when each bounded correction
stage is consistent through its own order. -/
theorem ofBirthFamily_consistent_iff :
    (ofBirthFamily D hbirth).Consistent ↔
      ∀ k, ((ofBirthFamily D hbirth).restrict {j | j.1 ≤ k}).LevelConsistent k := by
  rw [(ofBirthFamily D hbirth).consistent_iff]
  exact forall_congr' fun k =>
    (ofBirthFamily_levelEquivalent_restrict D hbirth (le_refl k)).consistent_iff

end Mei.DirectedDiagram
