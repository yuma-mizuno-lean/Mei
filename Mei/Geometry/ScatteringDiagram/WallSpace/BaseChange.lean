/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Truncation
public import Mei.Algebra.Lie.Graded.BaseChange
public import TauCeti.Geometry.ScatteringDiagram.WallSpace.BaseChange

/-!
# Scalar extension of directed wall spaces

The wall spaces over an algebra `S` are the images of `S ⊗[R] h` in
`S ⊗[R] L`. They satisfy the directed-wall axioms over any commutative coefficient
algebra, including nonflat ones. The geometric degree map and the integral normals
are unchanged. Scalar extension commutes with Lie-homomorphism images and with
degree truncation, so finite-order wall spaces can be extended before completion.

We use Mathlib's `Submodule.baseChange`, rather than identifying tensor products
with submodules without flatness. If `S` is flat, the existing equivalence
`Submodule.toBaseChange.toLinearEquiv S (H.wall n m)` identifies the tensor product
with the extended wall space via `baseChange_wall`. Bracket closure is the existing
`SetLike.GradedBracket.baseChange`, applied to pairs of degrees and normals.
-/

public section

open TauCeti (DirectedWallSpaces)

namespace TauCeti.DirectedWallSpaces

open Mei

variable {Γ Λ R S L : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [CommRing S] [Algebra R S]
  [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : Mei.PositiveDegrees Γ) [Mei.IsPositiveGrading d ℒ]

/-- Under the canonical truncation comparison, extending a wall space and then
truncating gives the scalar extension of its original truncated image. -/
theorem map_truncatedBaseChangeEquiv_wall (k : ℕ) (n : Γ) (m : Λ →+ ℤ) :
    (((H.baseChange S).truncated d k).wall n m).map
        (d.truncatedBaseChangeEquiv ℒ k).toLinearMap =
      ((H.truncated d k).wall n m).baseChange S := by
  have square : (d.truncatedBaseChangeEquiv ℒ k).toLinearMap.comp
      (d.degreeIdeal (fun n => (ℒ n).baseChange S) k).mkQ.toLinearMap =
        ((d.degreeIdeal ℒ k).mkQ.toLinearMap).baseChange S := by
    rw [← LieHom.coe_baseChange]
    apply LinearMap.ext
    intro z
    exact d.truncatedBaseChangeEquiv_mk ℒ k z
  rw [truncated_wall, baseChange_wall, ← Submodule.map_comp, square,
    truncated_wall, Submodule.baseChange_map]

end TauCeti.DirectedWallSpaces
