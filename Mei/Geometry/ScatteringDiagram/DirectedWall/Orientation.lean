/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.Convex.PolyhedralCochain.Basic

/-!
# Oriented supports of directed walls

A directed wall's stored integral normal gives its support a conormal orientation.
This realizes the wall as a generator of polyhedral cochains, with the same
positive side as the normal used for path products. The construction uses
`AlternatingMap.ofSubsingleton` to view a covector as an alternating one-form
and `Module.Ray.evalSign_rayOfNeZero` to identify its orientation sign.
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
  {H : DirectedWallSpaces ρ ℒ} (W : DirectedWall (d := d) h H)

/-- The support oriented by the positive side of the stored integral normal. -/
def toOrientedCell : OrientedCell h 1 := by
  let α := AlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1) (h.realCharacter W.normal)
  -- Evaluation of the standard covector-to-one-form equivalence.
  have hαapply (v : Fin 1 → V) : α v = h.realCharacter W.normal (v 0) := rfl
  have hα : α ≠ 0 := by
    intro hz
    apply W.normal_ne_zero
    apply h.realCharacter_injective
    ext v
    have he := congrArg (fun f : V [⋀^Fin 1]→ₗ[ℝ] ℝ => f (fun _ => v)) hz
    simpa only [hαapply, zero_apply, map_zero, LinearMap.zero_apply] using he
  refine ⟨W.support, W.rational_support, W.support_nonempty,
    W.finrank_direction_add_one, rayOfNeZero ℝ α hα, ?_⟩
  rw [Module.Ray.isConormal_rayOfNeZero_iff, Submodule.mem_conormalForms]
  intro v j hj
  have hv : v 0 = v j := congrArg v (Fin.eq_zero j).symm
  simpa only [hαapply, hv, LinearMap.mem_ker]
    using (W.direction_support ▸ hj : v j ∈ (h.realCharacter W.normal).ker)

@[simp]
theorem toOrientedCell_carrier : W.toOrientedCell.carrier = W.support := (rfl)

/-- The cochain orientation has exactly the sign of the wall's stored normal. -/
@[simp]
theorem evalSign_toOrientedCell (v : V) :
    W.toOrientedCell.orientation.evalSign (fun _ : Fin 1 => v) =
      SignType.sign (h.realCharacter W.normal v) := by
  unfold toOrientedCell
  rw [Module.Ray.evalSign_rayOfNeZero]
  rfl

end Mei.DirectedWall
