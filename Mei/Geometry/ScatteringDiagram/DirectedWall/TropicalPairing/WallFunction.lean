/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Map.Modulus
public import Mei.Algebra.Lie.Logarithmic.WallFunction.Map
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing

/-!
# Function walls under finite-index lattice changes

Let `P = DirectedWall.Pushforward.ofFiniteIndex T t ht hρ ν q hq hν` be the pushforward along
a finite-index tangent embedding `t : Λ → Λ'`, where `ν n ∘ t = q n • n` for integral
normals `n`, and let `n'` be any integral normal with `n' ∘ t = q n • n`, for instance `ν n`.
A tangent field `z^p ∂_n` is sent to `(q n)⁻¹ • z^{T p} ∂_{n'}`
(`Mei.DirectedWall.Pushforward.coe_ofFiniteIndex_lieHom_of_eq_single`), `T` maps the degrees
tangent to `n` to degrees tangent to `n'` (`Mei.map_tropicalTangentMonoid_intCast_le`), and the
completed function-wall label `exp(u ∂_n)` is sent to `exp(((q n)⁻¹ • T_* u) ∂_{n'})`
(`Mei.DirectedWall.Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp`).

**Ray-power comparison.** If `q n = r` is a natural number and `T_* f₀ = f₁ ^ r`, then
`exp(log(f₀) ∂_n)` is sent to `exp(log(f₁) ∂_{n'})`
(`Mei.DirectedWall.Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog`).
For primitive `n` and `n'` these labels have wall functions `f₀` and `f₁`, by
`Mei.completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog`. So the
wall function on the side of `Λ` is the `r`-th power of the wall function on the side of `Λ'`.
Every `f₀` has such an `r`-th root `f₁`
(`Mei.DirectedWall.Pushforward.exists_pow_eq_and_ofFiniteIndex_lieHom_completedMap_eq`).

When the degree lattice is shared and `T` is the identity, as for a lattice change that keeps
the coefficient variables, the pushed wall stays on its supported ray
(`Mei.DirectedWall.pushforward_ofFiniteIndex_id_ray`). A wall labelled by the ray factor of
`exp(log(f₀) ∂_n)` on its ray, as in the ray presentation of the function wall of `f₀`, is then
pushed to a wall labelled by the ray factor of `exp(log(f₁) ∂_{n'})` on the same ray
(`Mei.DirectedWall.pushforward_ofFiniteIndex_id_label`).

This is the wall-level comparison in the lattice change of Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1). There `t` is the
inclusion `M ⊆ ℓ⁻¹M₀`, and for `m° = r • m` with `m` primitive in `M`, the primitive normal of
`ℝm°` for `ℓ⁻¹M₀` restricts to `r` times the primitive normal for `M`, because
`ℓ = r · ind(m°)` (`Submodule.index_eq_mul_relIndex_ker_eval`). The comparison of the two
consistent completions themselves, which needs the identification of the pushed incoming walls
with the incoming walls over `ℓ⁻¹M₀` and the uniqueness of outgoing completions, is not
formalized here.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap SupportedRay GradedLieHom)

noncomputable section

namespace Mei

open LogarithmicVectorField TauCeti.Toric

namespace DirectedWall

universe u

variable {R Γ Λ Γ' Λ' : Type u} {V V' : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [AddCommGroup Λ'] [Module.Free ℤ Γ']
  [DecidableEq Γ] [DecidableEq Γ']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {i : Λ →+ V} {i' : Λ' →+ V'} {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

namespace Pushforward

variable (T : PositiveDegreeMap d e) (t : Λ →+ Λ') (ht : Function.Injective t)
  [t.range.FiniteIndex] (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n))
  (ν : (Λ →+ ℤ) → (Λ' →+ ℤ)) (q : (Λ →+ ℤ) → ℚ) (hq : ∀ m, 0 < q m)
  (hν : ∀ m x, (ν m (t x) : ℚ) = q m * m x) (n : Λ →+ ℤ) {n' : Λ' →+ ℤ}
  (hn' : ∀ x, (n' (t x) : ℚ) = q n * n x)

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "ℒ'" => tropicalVertexGrading (R := R) e ρ'
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ (AddMonoidHom.comp (Int.castAddHom R) n))
local notation "G'" => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ' (AddMonoidHom.comp (Int.castAddHom R) n'))
local notation "Φ" => completedTropicalTangentMap T (map_tropicalTangentMonoid_intCast_le T hρ hn')

omit [DecidableEq Γ] [DecidableEq Γ'] in
include hn' in
/-- Let `n'` be an integral normal with `n' ∘ t = q n • n`, for instance `ν n`. The
finite-index pushforward sends a field `z^p ∂_n` to `(q n)⁻¹ • z^{T p} ∂_{n'}`, also when `n`
does not vanish on the spatial degree of `p`. -/
theorem coe_ofFiniteIndex_lieHom_of_eq_single {p : Γ}
    (x : tropicalVertexLieAlgebra (R := R) d ρ)
    (hx : single ρ p ((Int.castAddHom R).comp n) = x.val) :
    ((ofFiniteIndex (h := h) (h' := h') T t ht hρ ν q hq hν).lieHom x).val =
      algebraMap ℚ R (q n)⁻¹ • single ρ' (T p) ((Int.castAddHom R).comp n') := by
  rw [coe_ofFiniteIndex_lieHom_of_homogeneous T t ht hρ ν q hq hν x _ hx,
    t.rationalDualEquiv_intCast_comp ht (hq n).ne' hn', ← algebraMap_smul R, map_smul]

/-- Let `n'` be an integral normal with `n' ∘ t = q n • n`, for instance `ν n`. The
finite-index pushforward sends the completed function-wall label `exp(u ∂_n)` to
`exp(((q n)⁻¹ • T_* u) ∂_{n'})`: the integral normal `n'` is kept and the denominator goes into
the coefficient. -/
theorem ofFiniteIndex_lieHom_completedMap_completedBCHExp (u : (G).completion) :
    (ofFiniteIndex (h := h) (h' := h') T t ht hρ ν q hq hν).lieHom.completedMap
        (d.completedBCHExp ℒ (completedTropicalTangentField d ρ ((Int.castAddHom R).comp n) u)) =
      e.completedBCHExp ℒ' (completedTropicalTangentField e ρ' ((Int.castAddHom R).comp n')
        (algebraMap ℚ R (q n)⁻¹ • Φ u)) :=
  GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField _ _
    (fun _ _ x hx => coe_ofFiniteIndex_lieHom_of_eq_single T t ht hρ ν q hq hν n hn' x hx) u

/-- **Ray-power comparison.** Let `n'` be an integral normal with `n' ∘ t = q n • n`, for
instance `ν n`. If `q n = r` and the tangent monomial map sends `f₀` to `f₁ ^ r`, the
finite-index pushforward sends the function-wall label `exp(log(f₀) ∂_n)` to
`exp(log(f₁) ∂_{n'})`. -/
theorem ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog {r : ℕ} (hr : q n = r)
    (f₀ : {u : (G).completion // u - 1 ∈ (G).completionIdeal 1})
    (f₁ : {u : (G').completion // u - 1 ∈ (G').completionIdeal 1})
    (hf : Φ f₀ = (f₁ : (G').completion) ^ r) :
    (ofFiniteIndex (h := h) (h' := h') T t ht hρ ν q hq hν).lieHom.completedMap
        (d.completedBCHExp ℒ (completedTropicalTangentField d ρ ((Int.castAddHom R).comp n)
          ((G).completedLog f₀))) =
      e.completedBCHExp ℒ' (completedTropicalTangentField e ρ' ((Int.castAddHom R).comp n')
        ((G').completedLog f₁)) := by
  refine GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_completedLog _ _
    (fun _ _ x hx => coe_ofFiniteIndex_lieHom_of_eq_single T t ht hρ ν q hq hν n hn' x hx) ?_
    f₀ f₁ hf
  rw [← map_natCast (algebraMap ℚ R), ← map_mul, ← hr, mul_inv_cancel₀ (hq n).ne', map_one]

/-- **Ray-power comparison for every function wall.** Let `n'` be an integral normal with
`n' ∘ t = q n • n` and let `q n = r` be a natural number. For every completed tangent series `f₀`
congruent to one there is an `r`-th root `f₁` of its image under the tangent monomial map, and
the finite-index pushforward sends `exp(log(f₀) ∂_n)` to `exp(log(f₁) ∂_{n'})`. -/
theorem exists_pow_eq_and_ofFiniteIndex_lieHom_completedMap_eq {r : ℕ} (hr : q n = r)
    (f₀ : {u : (G).completion // u - 1 ∈ (G).completionIdeal 1}) :
    ∃ f₁ : {u : (G').completion // u - 1 ∈ (G').completionIdeal 1},
      Φ f₀ = (f₁ : (G').completion) ^ r ∧
      (ofFiniteIndex (h := h) (h' := h') T t ht hρ ν q hq hν).lieHom.completedMap
          (d.completedBCHExp ℒ (completedTropicalTangentField d ρ ((Int.castAddHom R).comp n)
            ((G).completedLog f₀))) =
        e.completedBCHExp ℒ' (completedTropicalTangentField e ρ' ((Int.castAddHom R).comp n')
          ((G').completedLog f₁)) := by
  /- Take `f₁ = exp(r⁻¹ Φ(log f₀))`. Then `f₁ ^ r = exp(Φ(log f₀)) = Φ(f₀)`, and the comparison
  is `ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog`. -/
  have hr0 : (r : ℚ) ≠ 0 := hr ▸ (hq n).ne'
  have hx : algebraMap ℚ R (r : ℚ)⁻¹ • Φ ((G).completedLog f₀) ∈ (G').completionIdeal 1 := by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (completedTropicalTangentMap_mem_completionIdeal_one _ _
      ((G).completedLog_mem f₀))
  have hf : Φ f₀ = (G').completedExp ⟨_, hx⟩ ^ r := by
    rw [← AlgFiltration.completedExp_nsmul, ← (G).completedExp_completedLog f₀,
      completedTropicalTangentMap_completedExp]
    congr 1
    refine Subtype.ext ?_
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul R, smul_smul,
      ← map_natCast (algebraMap ℚ R), ← map_mul, mul_inv_cancel₀ hr0, map_one, one_smul]
  exact ⟨⟨_, (G').completedExp_sub_one_mem _⟩, hf,
    ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog T t ht hρ ν q hq hν n hn' hr
      f₀ _ hf⟩

end Pushforward

section SameDegrees

variable [Module.Free ℤ Γ] {ρ' : Γ →+ Λ'} {i' : Λ' →+ V'} {h' : IsIntegralLattice i'}
  (t : Λ →+ Λ') (ht : Function.Injective t) [t.range.FiniteIndex]
  (hρ : ∀ n ∈ d.monoid, ρ' (PositiveDegreeMap.id d n) = t (ρ n))
  (ν : (Λ →+ ℤ) → (Λ' →+ ℤ)) (q : (Λ →+ ℤ) → ℚ) (hq : ∀ m, 0 < q m)
  (hν : ∀ m x, (ν m (t x) : ℚ) = q m * m x)
  (W : DirectedWall (d := d) h (tropicalVertexWallSpaces (R := R) d ρ))

local notation "P" =>
  Pushforward.ofFiniteIndex (h := h) (h' := h') (PositiveDegreeMap.id d) t ht hρ ν q hq hν

/-- When the degree map is the identity, a finite-index pushforward keeps the supported ray. -/
theorem pushforward_ofFiniteIndex_id_ray : (W.pushforward P).ray = W.ray := by
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ _
  obtain ⟨p, hp⟩ := W.ray.rayDegrees_nonempty
  have hp' := W.degreeMap_mem_pushforward_rayDegrees P hp
  rw [Pushforward.ofFiniteIndex_degreeMap, PositiveDegreeMap.id_apply] at hp'
  exact SupportedRay.eq_of_mem_rayDegrees hp' hp

variable {n : Λ →+ ℤ} {n' : Λ' →+ ℤ}
  (hn' : ∀ x, (n' (t x) : ℚ) = q n * n x)

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ (AddMonoidHom.comp (Int.castAddHom R) n))
local notation "G'" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ' (AddMonoidHom.comp (Int.castAddHom R) n'))

/-- **Ray-power comparison of ray walls.** Let the degree map be the identity, let `n` be an
integral normal (in practice the normal of `W`), let `n'` be an integral normal with
`n' ∘ t = q n • n` (for instance `ν n`), and let `q n = r`. If `W` is labelled by the ray
factor of `exp(log(f₀) ∂_n)` on its ray and the tangent monomial map sends `f₀` to `f₁ ^ r`,
then the pushed wall is labelled by the ray factor of `exp(log(f₁) ∂_{n'})` on the same ray. -/
theorem pushforward_ofFiniteIndex_id_label {r : ℕ} (hr : q n = r)
    (f₀ : {u : (G).completion // u - 1 ∈ (G).completionIdeal 1})
    (f₁ : {u : (G').completion // u - 1 ∈ (G').completionIdeal 1})
    (hW : W.label = d.rayFactor _ (d.completedBCHExp _ (completedTropicalTangentField d ρ
      ((Int.castAddHom R).comp n) ((G).completedLog f₀))) W.ray)
    (hf : completedTropicalTangentMap (PositiveDegreeMap.id d)
      (map_tropicalTangentMonoid_intCast_le _ hρ hn') f₀ = (f₁ : (G').completion) ^ r) :
    (W.pushforward P).label = d.rayFactor _ (d.completedBCHExp _
      (completedTropicalTangentField d ρ' ((Int.castAddHom R).comp n')
        ((G').completedLog f₁))) W.ray := by
  rw [pushforward_label, hW, GradedLieHom.completedMap_rayFactor_of_forall_apply_eq _
    (fun _ => by rw [Pushforward.ofFiniteIndex_degreeMap, PositiveDegreeMap.id_apply]),
    Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog _ t ht hρ ν q hq hν
      _ hn' hr f₀ f₁ hf]

end SameDegrees

end DirectedWall

end Mei
