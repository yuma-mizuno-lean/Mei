/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Map
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom

/-!
# Finite-order directed wall spaces

The images of directed wall spaces in a degree quotient satisfy the same normal
and bracket laws. Lowering the cutoff sends each wall space onto its lower-order
image. Thus the finite-order spaces are compatible with the Lie truncation tower,
without a freeness or flatness assumption. Fixed-degree homomorphisms preserving wall
spaces preserve them at every finite order.

The construction uses `DirectedWallSpaces.map` on the canonical quotient maps.
-/

public section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ]

/-- Wall spaces at order `k` are the actual quotient images of the original spaces. -/
def truncated (k : ℕ) : DirectedWallSpaces ρ (d.truncatedGrading ℒ k) :=
  H.map (d.degreeIdeal ℒ k).mkQ (d.truncatedGrading ℒ k)
    (by intro n; rw [PositiveDegrees.truncatedGrading_eq]; exact le_rfl)

/-- Truncation takes each wall space to its image in the Lie quotient. -/
@[simp]
theorem truncated_wall (k : ℕ) (n : Γ) (m : Λ →+ ℤ) :
    (H.truncated d k).wall n m =
      (H.wall n m).map (d.degreeIdeal ℒ k).mkQ.toLinearMap := by
  rw [truncated, map_wall]

/-- The canonical graded quotient homomorphism preserves directed wall spaces. -/
theorem truncation_mem_wall (k : ℕ) (n : Γ) (m : Λ →+ ℤ) (x : L)
    (hx : x ∈ H.wall n m) :
    GradedLieHom.truncation d ℒ k x ∈ (H.truncated d k).wall n m := by
  rw [truncated_wall]
  exact Submodule.mem_map.mpr ⟨x, hx, (GradedLieHom.truncation_apply k x).symm⟩

/-- Every finite-order wall space maps onto its image at a lower cutoff. -/
theorem map_truncationMap_wall {k l : ℕ} (h : k ≤ l) (n : Γ) (m : Λ →+ ℤ) :
    ((H.truncated d l).wall n m).map (d.truncationMap ℒ h).toLinearMap =
      (H.truncated d k).wall n m := by
  have square : (d.truncationMap ℒ h).toLinearMap.comp
      (d.degreeIdeal ℒ l).mkQ.toLinearMap = (d.degreeIdeal ℒ k).mkQ.toLinearMap := by
    ext x
    simp
  rw [truncated_wall, ← Submodule.map_comp, square, truncated_wall]

end Mei.DirectedWallSpaces

namespace Mei.GradedLieHom

variable {Γ Λ R L L' : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] [DecidableEq Γ]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] {d : PositiveDegrees Γ}
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}

/-- A fixed-degree homomorphism preserving wall spaces preserves the wall spaces at every
finite order. -/
theorem truncatedMap_mem_truncated_wall (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m) (k : ℕ) {n : Γ} {m : Λ →+ ℤ}
    {x : d.truncatedLie ℒ k} (hx : x ∈ (H.truncated d k).wall n m) :
    f.truncatedMap k (by simp) x ∈ (H'.truncated d k).wall n m := by
  rw [DirectedWallSpaces.truncated_wall] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨f y, hf n m y hy, ?_⟩
  simpa only [LieIdeal.mkQ_apply, LieHom.coe_toLinearMap] using
    (f.truncatedMap_mk k (by simp) y).symm

end Mei.GradedLieHom
