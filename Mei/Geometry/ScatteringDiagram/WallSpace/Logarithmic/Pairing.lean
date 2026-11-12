/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Full
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Basic

/-!
# Tropical pairings preserve logarithmic wall spaces

Let `(T, S)` be a tropical pairing on all characters, and let `ν` assign to each integral
normal `m` of the source an integral normal `ν m` of the target such that `S` sends the
character of `m` into the `R`-line of the character of `ν m`. Then the Lie map of the pairing
sends the wall line of `z^n ∂_m` into the wall line of `z^{T n} ∂_{ν m}`, which is the
wall-space condition of `DirectedWall.Pushforward`. Tangency of `ν m` to `T n` is not
assumed: when it fails, the evaluation identity of the pairing forces the image to vanish
over a `ℚ`-algebra.

The pairing and the wall lines follow Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

noncomputable section

namespace Mei.TropicalPairing

open LogarithmicVectorField

variable {R Γ Λ Γ' Λ' : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') (⊤ : Submodule R (Λ →+ R)))

/-- If the character map sends the character of each integral normal `m` into the line of
the character of `ν m`, the Lie map of the pairing sends the wall space of degree `n` and
normal `m` into the wall space of degree `T n` and normal `ν m`. -/
theorem tropicalVertexGradedLieHom_mem_wall (ν : (Λ →+ ℤ) → (Λ' →+ ℤ))
    (hν : ∀ m, p.characterMap ⟨(Int.castAddHom R).comp m, Submodule.mem_top⟩ ∈
      R ∙ (Int.castAddHom R).comp (ν m))
    {n : Γ} {m : Λ →+ ℤ} {x : tropicalVertexLieAlgebra (R := R) d ρ}
    (hx : x ∈ (tropicalVertexWallSpaces d ρ).wall n m) :
    p.tropicalVertexGradedLieHom x ∈
      (tropicalVertexWallSpaces e ρ').wall (p.degreeMap n) (ν m) := by
  by_cases hn : n ∈ d.monoid
  swap
  · have hxp := (tropicalVertexWallSpaces d ρ).wall_le_piece n m hx
    rw [IsPositiveGrading.eq_bot (d := d) (ℒ := tropicalVertexGrading (R := R) d ρ) n
      (Or.inl hn), Submodule.mem_bot] at hxp
    simp [hxp]
  by_cases hm : m (ρ n) = 0
  swap
  · rw [(tropicalVertexWallSpaces d ρ).nontangent n m hm, Submodule.mem_bot] at hx
    simp [hx]
  obtain ⟨r, hr⟩ := (mem_tropicalVertexWallSpaces_iff_of_tangent d ρ n m hm x).mp hx
  let c : (⊤ : Submodule R (Λ →+ R)) := ⟨(Int.castAddHom R).comp m, Submodule.mem_top⟩
  have hx' : single ρ n (r • c).val = x.val := by
    rw [Submodule.coe_smul, map_smul, ← hr]
  rw [mem_tropicalVertexWallSpaces_iff, p.coe_tropicalVertexGradedLieHom_of_homogeneous x _ hx',
    Subtype.coe_eta, map_smul, map_smul]
  refine Submodule.smul_mem _ r ?_
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (hν m)
  by_cases ht : ν m (ρ' (p.degreeMap n)) = 0
  · rw [wallSubmodule_of_tangent ρ' _ _ ht, ← hs, map_smul]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
  · have hu : IsUnit ((ν m (ρ' (p.degreeMap n)) : ℤ) : R) := by
      simpa using (isUnit_iff_ne_zero.mpr
        (by exact_mod_cast ht : ((ν m (ρ' (p.degreeMap n)) : ℤ) : ℚ) ≠ 0)).map (algebraMap ℚ R)
    have hs0 : s = 0 := by
      have he := congrArg (fun χ : Λ' →+ R => χ (ρ' (p.degreeMap n))) hs
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, Int.coe_castAddHom,
        smul_eq_mul, p.eval_eq c hn, c, hm, Int.cast_zero] at he
      exact hu.mul_left_eq_zero.mp he
    rw [← hs, hs0, zero_smul, map_zero]
    exact Submodule.zero_mem _

end Mei.TropicalPairing
