/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Grouping

/-!
# The finite alphabet lift of `1 + c₀ x + c₁ x²`

On the horizontal axis `{y = 0}` of `ℝ²`, cooriented by `e₂*`, take the terms `c₀ x` and
`c₁ x²`, with exponents `m₀ = (1, 0)` and `m₁ = (2, 0)` in `M = ℤ²` (`axisInput`). Their letters
`v₀ = (m₀, e₀)` and `v₁ = (m₁, e₁)` lie on distinct supported rays of the finite alphabet
(`letterRay_zero_ne_letterRay_one`), so the alphabet wall function `1 + c₀ z^{v₀} + c₁ z^{v₁}`
splits into ray factors on many rays. The first projection `τ` lifts the letters to the positive
quadrant `ℕ²` of `L = ℤ²` with identity projection to `M`, sending them to `n₀ = (1, 0)` and
`n₁ = (2, 0)` (`liftFiniteAlphabet_axisInput_exponent`). Both images lie on the supported ray of
`e₁` (`axisPushforward_rayMap_letterRay`), so the image rays of the two letters are regrouped
into the single ray of the ambient primitive generator `e₁`. The pushforward of the alphabet ray
presentation is equivalent to the ray presentation of `1 + c₀ x + c₁ x²` in `ℕ²`
(`axisInput_pushforward_equivalent`), and the scattering classes correspond
(`axisInput_pushforward_scat`). Both exponents of the lift lie on the direction `e₁`, so for the
independent variables `c₀, c₁` its ray presentation is a positive wall representative, with
wall function `1 + c₀ x + c₁ x²` (`axisInput_liftFiniteAlphabet_isPositiveWallRepresentative`).

This is the check `1 + p₁ x + p₂ x²` of the finite alphabet lift in Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, §9.2 (arXiv:2503.03719v1).
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

namespace Mei.HyperplaneTermInput.Examples

open TauCeti.PositiveDegrees DirectedWall DirectedDiagram

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The exponents `m₀ = (1, 0)` and `m₁ = (2, 0)` of `x` and `x²`. -/
def axisExponent : Fin 2 → ℤ × ℤ := ![(1, 0), (2, 0)]

/-- The first exponent is `(1, 0)`. -/
@[simp]
theorem axisExponent_zero : axisExponent 0 = (1, 0) := by
  simp [axisExponent]

/-- The second exponent is `(2, 0)`. -/
@[simp]
theorem axisExponent_one : axisExponent 1 = (2, 0) := by
  simp [axisExponent]

/-- The second coordinate `e₂*` is a nonzero normal. -/
theorem snd_ne_zero : AddMonoidHom.snd ℤ ℤ ≠ 0 := fun h => by
  simpa using DFunLike.congr_fun h (0, 1)

/-- Both exponents are tangent to the horizontal axis. -/
theorem snd_axisExponent (α : Fin 2) : AddMonoidHom.snd ℤ ℤ (axisExponent α) = 0 := by
  fin_cases α <;> simp

/-- The alphabet input of the terms `c₀ x` and `c₁ x²` on the horizontal axis. -/
def axisInput : HyperplaneTermInput (PositiveDegrees.finiteAlphabet axisExponent)
    (AddMonoidHom.fst (ℤ × ℤ) (Fin 2 → ℤ)) Unit (Fin 2) :=
  finiteAlphabet (fun _ => AddMonoidHom.snd ℤ ℤ) (fun _ => snd_ne_zero) (fun _ => 0)
    (fun _ => ()) axisExponent fun α => snd_axisExponent α

/-- Every hyperplane of the alphabet input has the normal `e₂*`. -/
@[simp]
theorem axisInput_normal : axisInput.normal = fun _ => AddMonoidHom.snd ℤ ℤ := by
  simp [axisInput]

/-- The alphabet input has the letters as exponents. -/
@[simp]
theorem axisInput_exponent : axisInput.exponent = letter axisExponent := by
  simp [axisInput]

/-- The first projection `ℤ² × (Fin 2 → ℤ) → ℤ²`, used as the lift `τ`. -/
local notation "τ" => AddMonoidHom.fst (ℤ × ℤ) (Fin 2 → ℤ)

/-- The lift `τ` sends each letter into the positive quadrant `ℕ²`. -/
theorem axisExponent_mem (α : Fin 2) : τ (letter axisExponent α) ∈ ℕ².monoid := by
  fin_cases α <;> simp [Fin.forall_fin_two]

/-- The lift `τ` sends each letter to a nonzero degree. -/
theorem axisExponent_ne_zero (α : Fin 2) : τ (letter axisExponent α) ≠ 0 := by
  fin_cases α <;> simp

/-- The identity projection sends the lift of each letter to its exponent. -/
theorem id_axisExponent (α : Fin 2) :
    AddMonoidHom.id (ℤ × ℤ) (τ (letter axisExponent α)) = axisExponent α := by
  simp

/-- The lifted input has the exponents `n₀ = (1, 0)` and `n₁ = (2, 0)`. -/
theorem liftFiniteAlphabet_axisInput_exponent :
    (axisInput.liftFiniteAlphabet axisExponent_mem axisExponent_ne_zero
      id_axisExponent).exponent = axisExponent := by
  funext α
  simp [axisInput]

/-- The two letters lie on distinct supported rays of the finite alphabet. -/
theorem letterRay_zero_ne_letterRay_one : letterRay axisExponent 0 ≠ letterRay axisExponent 1 :=
  (letterRay_injective axisExponent).ne (by decide)

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- Pushforward data along the finite alphabet lift `τ`, over `ℚ`. -/
local notation "Pτ" => Pushforward.ofFiniteAlphabetLift (R := ℚ) (g := h) axisExponent_mem
  axisExponent_ne_zero id_axisExponent

/-- The ray map of the pushforward data sends the rays of both letters to the supported ray of
`e₁` in `ℕ²`. -/
theorem axisPushforward_rayMap_letterRay (α : Fin 2) :
    (Pτ).rayMap (letterRay axisExponent α) =
      Module.Basis.positiveDegreesRay (Module.Basis.finTwoProd ℤ) 0 := by
  rw [Pushforward.ofFiniteAlphabetLift_rayMap, SupportedRay.map_eq_iff_exists_mem_rayDegrees]
  refine ⟨letter axisExponent α, ?_, ?_⟩
  · simpa using (SupportedRay.generator_mem_rayDegrees_iff (letterRay axisExponent α)).mpr
      (by simp)
  · refine SupportedRay.mem_rayDegrees.mpr
      ⟨by simpa using axisExponent_mem α, α.val + 1, by omega, ?_⟩
    fin_cases α <;> simp [finiteAlphabetLift_apply]

variable (c : Fin 2 → ℚ)

/-- The pushforward of the alphabet ray presentation of `1 + c₀ z^{v₀} + c₁ z^{v₁}` is
equivalent to the ray presentation of `1 + c₀ x + c₁ x²` in `ℕ²`. -/
theorem axisInput_pushforward_equivalent :
    ((axisInput.diagram h c).pushforward (Pτ)).Equivalent
      ((axisInput.liftFiniteAlphabet axisExponent_mem axisExponent_ne_zero
        id_axisExponent).diagram h c) :=
  axisInput.diagram_pushforward_ofFiniteAlphabetLift_equivalent _ _ _ h c

/-- The pushforward of the scattering class of the alphabet input is the scattering class of
`1 + c₀ x + c₁ x²` on the horizontal axis. -/
theorem axisInput_pushforward_scat :
    DirectedDiagram.Class.pushforward (Pτ)
        ((axisInput.diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((axisInput.liftFiniteAlphabet axisExponent_mem axisExponent_ne_zero
        id_axisExponent).diagram h c).Scat
        (fun _ => ofHyperplaneRayFactors_full ..) :=
  axisInput.pushforward_scat_liftFiniteAlphabet _ _ _ h c

section Positive

open scoped Mei.TropicalVertexCoefficientAction

local instance : Fact (ℕ².monoid ≤ (⊤ : AddSubmonoid (ℤ × ℤ))) := ⟨le_top⟩

/-- For the independent variables `c₀, c₁` over `ℚ` and the full coefficient lattice `ℤ²`, the
ray presentation of `1 + c₀ x + c₁ x²` on the horizontal axis of `ℕ²` is a positive wall
representative: its grouped wall function has coefficients in `ℕ[c₀, c₁]`. -/
theorem axisInput_liftFiniteAlphabet_isPositiveWallRepresentative :
    ((axisInput.liftFiniteAlphabet axisExponent_mem axisExponent_ne_zero id_axisExponent).diagram
        h (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℚ)).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration (R := MvPolynomial (Fin 2) ℚ) ℕ²
        ⊤).completedBCHAction ℕ²
        (tropicalVertexGrading (R := MvPolynomial (Fin 2) ℚ) ℕ² (AddMonoidHom.id (ℤ × ℤ))))
      (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ))
        (MvPolynomial.map (σ := Fin 2) (Nat.castRingHom ℚ))).rangeS
      (AddMonoidHom.id (ℤ × ℤ)) :=
  axisInput.isPositiveWallRepresentative_liftFiniteAlphabet_diagram axisExponent_mem
    axisExponent_ne_zero id_axisExponent h MvPolynomial.X (fun _ => (1, 0))
    (fun α => ⟨α.val + 1, by omega, by fin_cases α <;> simp⟩) ⊤
    (fun _ => ⟨(0, 1), trivial, trivial, by simp⟩) _
    fun α => ⟨MvPolynomial.X α, MvPolynomial.map_X _ α⟩

end Positive

end Mei.HyperplaneTermInput.Examples
