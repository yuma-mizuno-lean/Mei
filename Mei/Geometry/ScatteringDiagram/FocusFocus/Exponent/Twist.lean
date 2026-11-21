/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.ExponentSystem.Iso
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Exponent.System

/-!
# Height twists of the focus-focus exponent system

The exponent lattice of the focus-focus puncture has coordinates `(a, b, h)`: the tangent
coordinates `(a, b)` and the smoothing exponent `h`. Its frame change `upperExponent` is the
shear `(a, b, h) ↦ (a, b - a, h)`, which fixes the first tangent coordinate `a`.

For `c : ℤ`, the height twist `heightTwist c : (a, b, h) ↦ (a, b, h + c a)` therefore commutes
with every frame change and preserves the projection `(a, b, h) ↦ (a, b)` to the tangent
lattice, so it is an automorphism of the focus-focus exponent system with constant components
(`Mei.FocusFocus.exponentSystemTwist`). The twists form a group homomorphism from
`Multiplicative ℤ` to the automorphism group of the exponent system
(`Mei.FocusFocus.exponentSystemTwistHom`), which is injective
(`Mei.FocusFocus.exponentSystemTwistHom_injective`): the focus-focus exponent system has
automorphisms over the tangent lattice that are not the identity.

The geometry is the focus-focus local model of Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2).
-/

public section

open Set Topology Manifold

namespace Mei.FocusFocus

attribute [local instance] chartedSpace hasGroupoid

/-- The height twist `(a, b, h) ↦ (a, b, h + c a)` of the exponent lattice by `c` times the
first tangent coordinate. -/
def heightTwist (c : ℤ) : (ℤ × ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ × ℤ) :=
  (LinearEquiv.refl ℤ ℤ).skewProd (LinearEquiv.refl ℤ (ℤ × ℤ)) ((0 : ℤ →ₗ[ℤ] ℤ).prod (c • .id))

/-- The height twist by `c` adds `c` times the first tangent coordinate to the smoothing
exponent. -/
@[simp] theorem heightTwist_apply (c : ℤ) (q : ℤ × ℤ × ℤ) :
    heightTwist c q = (q.1, q.2.1, q.2.2 + c * q.1) := by
  ext <;> simp [heightTwist]

/-- The height twist by `0` is the identity. -/
@[simp] theorem heightTwist_zero : heightTwist 0 = LinearEquiv.refl ℤ _ := by
  ext q <;> simp

/-- Height twists add: twisting by `d` and then by `c` is twisting by `c + d`. -/
theorem heightTwist_add (c d : ℤ) :
    heightTwist (c + d) = (heightTwist d).trans (heightTwist c) := by
  ext q <;> simp only [heightTwist_apply, LinearEquiv.trans_apply, add_mul, add_assoc,
    add_comm (c * q.1)]

/-- The height twist commutes with the upper exponent shear. -/
theorem heightTwist_upperExponent (c : ℤ) (q : ℤ × ℤ × ℤ) :
    heightTwist c (upperExponent q) = upperExponent (heightTwist c q) := by
  simp

/-- The height twist does not change the spatial direction. -/
theorem exponentProjection_heightTwist (c : ℤ) (q : ℤ × ℤ × ℤ) :
    exponentProjection (heightTwist c q) = exponentProjection q := by
  simp

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The height twist by `c` as an automorphism of the focus-focus exponent system, with the
constant component `heightTwist c` in every frame. -/
noncomputable def exponentSystemTwist (c : ℤ) : (exponentSystem h).Iso (exponentSystem h) :=
  Toric.ExponentSystem.Iso.ofAddEquiv (heightTwist c).toAddEquiv
    (fun _ _ _ hx q => by
      rw [exponentSystem_coordChange_of_mem h hx]
      exact latticeTransition_comm (heightTwist_upperExponent c) _ _ _ q)
    (fun _ q => by simp)

/-- Every component of the height twist automorphism is the height twist. -/
@[simp]
theorem exponentSystemTwist_app (c : ℤ) (e : atlas (ℝ × ℝ) regularLocus) (p : regularLocus)
    (hp : p ∈ e.val.source) :
    (exponentSystemTwist h c).app e p hp = (heightTwist c).toAddEquiv := by
  rw [exponentSystemTwist, Toric.ExponentSystem.Iso.ofAddEquiv_app]

/-- The height twists of the focus-focus exponent system, as a group homomorphism from
`Multiplicative ℤ` to its automorphism group. -/
noncomputable def exponentSystemTwistHom :
    Multiplicative ℤ →* (exponentSystem h).Iso (exponentSystem h) where
  toFun c := exponentSystemTwist h c.toAdd
  map_one' := Toric.ExponentSystem.Iso.ext fun e p hp q => by
    simp only [exponentSystemTwist_app, toAdd_one, heightTwist_zero,
      Toric.ExponentSystem.Iso.one_def, Toric.ExponentSystem.Iso.refl_app,
      LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply, LinearEquiv.refl_apply,
      AddEquiv.refl_apply]
  map_mul' c d := Toric.ExponentSystem.Iso.ext fun e p hp q => by
    simp only [exponentSystemTwist_app, toAdd_mul, heightTwist_add,
      Toric.ExponentSystem.Iso.mul_def, Toric.ExponentSystem.Iso.trans_app, AddEquiv.trans_apply,
      LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply, LinearEquiv.trans_apply]

/-- The height twist homomorphism sends `c` to the height twist by `c`. -/
@[simp]
theorem exponentSystemTwistHom_apply (c : Multiplicative ℤ) :
    exponentSystemTwistHom h c = exponentSystemTwist h c.toAdd := (rfl)

/-- Distinct height twists are distinct automorphisms of the focus-focus exponent system. -/
theorem exponentSystemTwistHom_injective : Function.Injective (exponentSystemTwistHom h) := by
  intro c d hcd
  have hp : ((1, 0) : ℝ × ℝ) ∈ regularLocus := by simp
  have key (c : Multiplicative ℤ) :
      (exponentSystemTwistHom h c).app (achart (ℝ × ℝ) ⟨(1, 0), hp⟩) ⟨(1, 0), hp⟩
        (mem_achart_source _ _) (1, 0, 0) = (1, 0, c.toAdd) := by
    rw [exponentSystemTwistHom_apply, exponentSystemTwist_app, LinearEquiv.coe_toAddEquiv,
      LinearEquiv.coe_addEquiv_apply, heightTwist_apply, mul_one, zero_add]
  have := (key c).symm.trans (hcd ▸ key d)
  simpa only [Prod.mk.injEq, true_and, EmbeddingLike.apply_eq_iff_eq] using this

end Mei.FocusFocus
