/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.RestrictScalars
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.Examples
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Specialization

/-!
# Pushing tropical vertex diagrams from `ℚ[X]` to `ℚ` along `(a, b) ↦ (2a, b)`

On the positive quadrant `ℕ²` of `ℤ²`, with identity projection to the plane `ℝ²`, evaluation
of the coefficients at `X = 1` is a `ℚ`-linear fixed-degree map `evalOne` from the tropical
vertex algebra over `ℚ[X]` to the one over `ℚ`, preserving the wall spaces restricted to `ℚ`.
Composing it with the scalar restriction of the finite-index pushforward
`DirectedWall.Pushforward.Examples.doubleFirstPushforward` along `(a, b) ↦ (2a, b)` gives
degree-changing pushforward data `evalDoubleFirstPushforward` from the restricted tropical
vertex wall spaces over `ℚ[X]` to those over `ℚ`.

* The field `X z^{e₂} ∂_{e₁*}` is sent to `(1/2) z^{e₂} ∂_{e₁*}`: the coefficient `X` is
  evaluated at `1`, and the rational inverse dual of `e₁*` contributes the factor `1/2`
  (`coe_evalDoubleFirstPushforward_lieHom_single`).
* The cross-ring pushforward of every tropical vertex diagram over `ℚ[X]` along these data is
  the coefficient change along `evalOne` followed by the pushforward along `(a, b) ↦ (2a, b)`
  over `ℚ` (`pushforwardRestrictScalars_evalDoubleFirstPushforward`).
* The vertical axis `{x = 0}` over `ℚ[X]`, with any label, is pushed to an incoming wall over
  `ℚ` with the normal `e₁*` (`verticalAxis_pushforwardRestrictScalars_normal`,
  `verticalAxis_pushforwardRestrictScalars_incoming`).
* Outgoing completions over `ℚ[X]` are pushed to outgoing completions over `ℚ`, and the
  scattering class of a full-hyperplane input over `ℚ[X]` is pushed to the scattering class of
  the pushed input (`isOutgoingCompletion_evalDoubleFirstPushforward`,
  `pushforwardRestrictScalars_scat_evalDoubleFirstPushforward`).

The coefficient changes and pushforwards along tropical pairings are those of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram.Examples

open LogarithmicVectorField TauCeti.Toric DirectedWall DirectedWall.Pushforward.Examples
open Polynomial

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

local notation "ρ₀" => AddMonoidHom.id (ℤ × ℤ)

/-- Evaluation of the coefficients at `X = 1`, `z^n ∂_m ↦ z^n ∂_(m(1))`, as a `ℚ`-linear
fixed-degree map from the tropical vertex algebra of the quadrant over `ℚ[X]` to the one
over `ℚ`. -/
def evalOne : GradedLieHom (PositiveDegreeMap.id ℕ²)
    (fun n => (tropicalVertexGrading (R := ℚ[X]) ℕ² ρ₀ n).restrictScalars ℚ)
    (fun n => (tropicalVertexGrading (R := ℚ) ℕ² ρ₀ n).restrictScalars ℚ) :=
  coefficientMonoidGradedLieHom ρ₀ (aeval (1 : ℚ)) ℕ².monoid 1 ℕ² le_rfl

/-- Evaluation at `X = 1` preserves the tropical vertex wall spaces restricted to `ℚ`. -/
theorem evalOne_mem_wall (n : ℤ × ℤ) (m : ℤ × ℤ →+ ℤ) (x : tropicalVertexLieAlgebra ℕ² ρ₀)
    (hx : x ∈ ((tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀).restrictScalars ℚ).wall n m) :
    evalOne x ∈ ((tropicalVertexWallSpaces (R := ℚ) ℕ² ρ₀).restrictScalars ℚ).wall n m :=
  coefficientMonoidGradedLieHom_mem_wall ℕ² ρ₀ _ _ 1 le_rfl n m x hx

variable (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- Degree-changing pushforward data from the tropical vertex wall spaces of the quadrant over
`ℚ[X]` to those over `ℚ`, both restricted to `ℚ`: evaluate the coefficients at `X = 1`, then
push forward along `(a, b) ↦ (2a, b)`. -/
def evalDoubleFirstPushforward :
    Pushforward ℕ² ℕ² h h ((tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀).restrictScalars ℚ)
      ((tropicalVertexWallSpaces (R := ℚ) ℕ² ρ₀).restrictScalars ℚ) :=
  ((doubleFirstPushforward h).restrictScalars ℚ).comp
    (Pushforward.ofFixedDegree evalOne evalOne_mem_wall)

/-- Evaluation at `X = 1` sends the field `X z^{e₂} ∂_{e₁*}` over `ℚ[X]` to the field
`z^{e₂} ∂_{e₁*}` over `ℚ`. -/
theorem coe_evalOne_single :
    (evalOne ⟨single ρ₀ (0, 1) ((X : ℚ[X]) • (Int.castAddHom ℚ[X]).comp (AddMonoidHom.fst ℤ ℤ)),
        single_mem_tropicalVertexLieAlgebra (R := ℚ[X]) ℕ² ρ₀ zero_one_mem (by simp)
          ((X : ℚ[X]) • (Int.castAddHom ℚ[X]).comp (AddMonoidHom.fst ℤ ℤ)) (by simp)⟩).val =
      single ρ₀ (0, 1) ((Int.castAddHom ℚ).comp (AddMonoidHom.fst ℤ ℤ)) := by
  rw [evalOne, coe_coefficientMonoidGradedLieHom_of_homogeneous ρ₀ (aeval (1 : ℚ)) ℕ².monoid 1
    ℕ² le_rfl zero_one_mem _ ((X : ℚ[X]) • (Int.castAddHom ℚ[X]).comp (AddMonoidHom.fst ℤ ℤ)) rfl]
  congr 1
  ext x
  simp

/-- The cross-ring pushforward along `evalDoubleFirstPushforward` is the coefficient change
along `evalOne` followed by the pushforward along `(a, b) ↦ (2a, b)` over `ℚ`. -/
theorem pushforwardRestrictScalars_evalDoubleFirstPushforward {ι : Type*}
    (D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀) ι) :
    D.pushforwardRestrictScalars (evalDoubleFirstPushforward h) =
      (D.mapRestrictScalars evalOne evalOne_mem_wall).pushforward (doubleFirstPushforward h) := by
  rw [evalDoubleFirstPushforward, ← pushforwardRestrictScalars_pushforwardRestrictScalars,
    pushforwardRestrictScalars_ofFixedDegree, pushforwardRestrictScalars_restrictScalars]

/-- Outgoing completions over `ℚ[X]` are pushed to outgoing completions over `ℚ` of the pushed
input. -/
theorem isOutgoingCompletion_evalDoubleFirstPushforward {ι₀ ι' : Type*}
    {D₀ : ι₀ → DirectedWall (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀)}
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀) (ι₀ ⊕ ι')}
    (hE : IsOutgoingCompletion D₀ E) :
    IsOutgoingCompletion (fun j => (D₀ j).pushforwardRestrictScalars (evalDoubleFirstPushforward h))
      (E.pushforwardRestrictScalars (evalDoubleFirstPushforward h)) :=
  hE.pushforwardRestrictScalars

/-- The scattering class of a full-hyperplane input over `ℚ[X]` is pushed to the scattering
class of the pushed input over `ℚ`. -/
theorem pushforwardRestrictScalars_scat_evalDoubleFirstPushforward {ι : Type}
    (D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀) ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a}) :
    Class.pushforwardRestrictScalars (evalDoubleFirstPushforward h) (D.Scat hfull) =
      (D.pushforwardRestrictScalars (evalDoubleFirstPushforward h)).Scat
        (D.pushforwardRestrictScalars_fullHyperplane _ hfull) :=
  D.pushforwardRestrictScalars_scat _ hfull

section VerticalAxis

variable (g : (tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀).wallGroup
  (Module.Basis.positiveDegreesRay (Module.Basis.finTwoProd ℤ) 1) (AddMonoidHom.fst ℤ ℤ))

/-- The vertical axis `{x = 0}` of `ℝ²` as a wall over `ℚ[X]` on the ray `e₂`, with normal
`e₁*`. -/
def verticalAxis : DirectedWall (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ[X]) ℕ² ρ₀) :=
  ofAffineHyperplane _ _ (AddMonoidHom.fst ℤ ℤ)
    (fun he => by simpa using DFunLike.congr_fun he (1, 0)) 0 _ (by simp) g

/-- The pushed vertical axis keeps the normal `e₁*`. -/
theorem verticalAxis_pushforwardRestrictScalars_normal :
    ((verticalAxis h g).pushforwardRestrictScalars (evalDoubleFirstPushforward h)).normal =
      AddMonoidHom.fst ℤ ℤ := by
  simp [verticalAxis, evalDoubleFirstPushforward]

/-- The pushed vertical axis is incoming, since the vertical axis is. -/
theorem verticalAxis_pushforwardRestrictScalars_incoming :
    ((verticalAxis h g).pushforwardRestrictScalars (evalDoubleFirstPushforward h)).Incoming :=
  (incoming_pushforwardRestrictScalars_iff _ _).mpr (ofAffineHyperplane_incoming ..)

end VerticalAxis

end Mei.DirectedDiagram.Examples
