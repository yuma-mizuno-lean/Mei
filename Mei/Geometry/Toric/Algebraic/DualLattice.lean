/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mei.Geometry.Toric.Algebraic.RationalFunctional

/-!
# The integral dual lattice

The real extensions of integral characters form an actual integral lattice in
the real dual space. This identifies the supplier's `realCharacter` map with
the base-change map for the integral dual, transported from linear maps to
additive characters.

Evaluation on lattice vectors is compatible with this dual lattice. In
particular, evaluating a real functional on an original lattice vector is the
real extension, for the dual lattice, of integral evaluation at that vector.
For normed spaces, the same construction supplies the integral lattice in the
continuous dual, where these evaluation maps are rational functionals.
It transports the algebraic dual lattice along Mathlib's
`LinearMap.toContinuousLinearMap` using `TauCeti.Toric.isIntegralLattice_congr`.
-/

public section

namespace TauCeti.Toric.IsIntegralLattice

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- Real extension of additive characters is the base-change map on the
integral linear dual, under the canonical additive-to-linear identification. -/
theorem realCharacter_toIntLinearMap (h : IsIntegralLattice i) :
    h.realCharacter.toIntLinearMap =
      h.isBaseChange.toDual.comp (addMonoidHomLequivInt ℤ).toLinearMap := by
  apply LinearMap.ext
  intro m
  simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  symm
  apply h.eq_realCharacter
  intro n
  simpa using h.isBaseChange.toDual_comp_apply (addMonoidHomLequivInt ℤ m) n

/-- The real extensions of integral characters form an integral lattice in
the real dual space, including finite freeness and the actual base-change datum. -/
theorem dual (h : IsIntegralLattice i) : IsIntegralLattice h.realCharacter := by
  let _ := h.free
  let _ := h.finite
  let e : (N →+ ℤ) ≃ₗ[ℤ] Module.Dual ℤ N := addMonoidHomLequivInt ℤ
  have hbase : IsBaseChange ℝ h.realCharacter.toIntLinearMap ↔
      IsBaseChange ℝ h.isBaseChange.toDual :=
    IsBaseChange.iff_of_equiv_comm e (LinearEquiv.refl ℝ (Module.Dual ℝ V))
      h.realCharacter_toIntLinearMap.symm
  exact ⟨(Module.Free.iff_of_equiv e).mpr inferInstance,
    (Module.Finite.equiv_iff e).mpr inferInstance, hbase.mpr h.isBaseChange.dual⟩

/-- Under the dual lattice, integral evaluation at `n` extends to real
evaluation at `i n`. This is the canonical double-dual compatibility on lattice vectors. -/
@[simp]
theorem dual_realCharacter_eval (h : IsIntegralLattice i) (n : N) :
    h.dual.realCharacter (AddMonoidHom.eval n) = (Module.Dual.eval ℝ V) (i n) := by
  symm
  apply h.dual.eq_realCharacter
  intro m
  simp

end TauCeti.Toric.IsIntegralLattice

namespace TauCeti.Toric.IsIntegralLattice

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- Real extension of integral characters into the continuous real dual.
The finite dimensionality needed for continuity follows from the lattice. -/
noncomputable def continuousRealCharacter (h : IsIntegralLattice i) :
    (N →+ ℤ) →+ (V →L[ℝ] ℝ) := by
  letI := h.finiteDimensional
  exact LinearMap.toContinuousLinearMap.toAddMonoidHom.comp h.realCharacter

/-- Continuous real extension has the same values as algebraic real extension. -/
@[simp]
theorem continuousRealCharacter_apply (h : IsIntegralLattice i) (m : N →+ ℤ) (x : V) :
    h.continuousRealCharacter m x = h.realCharacter m x := (rfl)

/-- Integral characters form an integral lattice in the continuous real dual. -/
theorem continuousDual (h : IsIntegralLattice i) :
    IsIntegralLattice h.continuousRealCharacter := by
  let _ := h.finiteDimensional
  exact (isIntegralLattice_congr (AddEquiv.refl (N →+ ℤ))
    LinearMap.toContinuousLinearMap (fun _ => rfl)).mp h.dual

/-- Evaluation on an original lattice vector is the real extension of integral
evaluation for the continuous dual lattice. -/
@[simp]
theorem continuousDual_realCharacter_eval (h : IsIntegralLattice i) (n : N) :
    h.continuousDual.realCharacter (AddMonoidHom.eval n) =
      (ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap := by
  symm
  apply h.continuousDual.eq_realCharacter
  intro m
  simp

/-- Evaluation at a lattice vector is rational for the continuous dual lattice. -/
theorem isRationalFunctional_continuousDual_eval (h : IsIntegralLattice i) (n : N) :
    Mei.Toric.IsRationalFunctional h.continuousDual
      (ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap := by
  rw [← continuousDual_realCharacter_eval]
  exact Mei.Toric.IsRationalFunctional.realCharacter h.continuousDual
    (AddMonoidHom.eval n).toIntLinearMap

end TauCeti.Toric.IsIntegralLattice
