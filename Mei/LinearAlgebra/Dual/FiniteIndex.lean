/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Algebra.Rat

/-!
# Rational characters along finite-index embeddings

An injective additive map with finite-index image induces an equivalence on
characters valued in a rational algebra. The forward map extends a
character across the embedding; the inverse restricts it. No freeness or finite
rank assumption on the additive groups is needed.

The extension divides evaluation on an index multiple by that index. We use
Mathlib's `AddMonoidHom.ofInjective` to invert the map onto its range and
`LinearMap.lcomp` to bundle character restriction. This is the rational inverse
dual needed to transport logarithmic derivations through lattice embeddings.
-/

public section

noncomputable section

namespace AddMonoidHom

variable {M N R : Type*} [AddCommGroup M] [AddCommGroup N]
  [Ring R] [Algebra ℚ R]

/-- Extend rational-algebra-valued characters through an injective additive map
with finite-index image. Its inverse is precomposition with the embedding. -/
def rationalDualEquiv (f : M →+ N) (hf : Function.Injective f) [f.range.FiniteIndex] :
    (M →+ R) ≃ₗ[R] (N →+ R) := by
  let restriction : (N →+ R) →ₗ[R] (M →+ R) :=
    (addMonoidHomLequivInt R).symm.toLinearMap.comp
      ((LinearMap.lcomp R R f.toIntLinearMap).comp (addMonoidHomLequivInt R).toLinearMap)
  have restriction_apply (a : N →+ R) (x : M) : restriction a x = a (f x) := rfl
  let c := f.range.index
  have hc : (c : ℚ) ≠ 0 := by exact_mod_cast (f.range.index_ne_zero)
  let g : N →+ M := (ofInjective hf).symm.toAddMonoidHom.comp
    ((nsmulAddMonoidHom c).codRestrict f.range (fun y => f.range.nsmul_index_mem y))
  have hfg (y : N) : f (g y) = c • y := apply_ofInjective_symm hf _
  have hgf (x : M) : g (f x) = c • x := by
    apply hf
    simp [hfg]
  refine (LinearEquiv.ofBijective restriction ⟨?_, ?_⟩).symm
  · intro a b hab
    ext y
    have h : c • a y = c • b y := by
      simpa only [restriction_apply, hfg, map_nsmul] using congrArg (fun m : M →+ R => m (g y)) hab
    have h' : (c : ℚ) • a y = (c : ℚ) • b y := by
      simpa only [Nat.cast_smul_eq_nsmul ℚ] using h
    simpa only [inv_smul_smul₀ hc] using congrArg (fun r : R => (c : ℚ)⁻¹ • r) h'
  · intro m
    refine ⟨(c : ℚ)⁻¹ • m.comp g, ?_⟩
    ext x
    rw [restriction_apply, smul_apply, comp_apply, hgf, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hc]

/-- The inverse of rational character extension is restriction. -/
@[simp]
theorem rationalDualEquiv_symm_apply (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : N →+ R) :
    (f.rationalDualEquiv hf).symm m = m.comp f := (rfl)

/-- Restricting the extended character recovers the original character. -/
@[simp]
theorem rationalDualEquiv_apply_map (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : M →+ R) (x : M) :
    f.rationalDualEquiv hf m (f x) = m x := by
  have h := (f.rationalDualEquiv hf).symm_apply_apply m
  rw [rationalDualEquiv_symm_apply] at h
  exact congrArg (fun a : M →+ R => a x) h

/-- An extension is characterized by its restriction to the source. -/
theorem rationalDualEquiv_eq_iff (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : M →+ R) (a : N →+ R) :
    f.rationalDualEquiv hf m = a ↔ a.comp f = m := by
  rw [← rationalDualEquiv_symm_apply (R := R) f hf]
  constructor
  · rintro rfl
    exact (f.rationalDualEquiv hf).symm_apply_apply m
  · intro h
    rw [← h]
    exact (f.rationalDualEquiv hf).apply_symm_apply a

/-- Evaluate an extended character by dividing any nonzero integral multiple
that lies in the image of the embedding. -/
theorem rationalDualEquiv_apply_of_map_eq_nsmul (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : M →+ R) {x : M} {y : N} {k : ℕ}
    (hk : k ≠ 0) (h : f x = k • y) :
    f.rationalDualEquiv hf m y = (k : ℚ)⁻¹ • m x := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have he : (k : ℚ) • f.rationalDualEquiv hf m y = m x := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← h, rationalDualEquiv_apply_map]
  simpa only [inv_smul_smul₀ hk'] using congrArg (fun r : R => (k : ℚ)⁻¹ • r) he

end AddMonoidHom
