/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import Mei.RingTheory.FilteredAlgebra.Completion
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Completed scalars on filtered modules

Compatible ring and module filtrations induce scalar multiplication on their
finite-order quotients and completions. The completed action is computed by
the finite-order projections, extends the original scalar action, and adds
filtration orders. In particular, the induced filtrations remain compatible in
Mathlib's `IsModuleFiltration` sense.

The finite-order module structures use `Module.IsTorsionBySet.module` rather
than a new quotient construction. The compatible-family action follows the
componentwise construction used for `AdicCompletion` in Mathlib, but allows
arbitrary decreasing compatible filtrations over associative rings.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : AlgFiltration R) (G : ModuleFiltration R M)
  [IsModuleFiltration F.orderDual (fun k => F.ideal (k.ofDual + 1))
    G.filtration (fun k => G.submodule (k.ofDual + 1))]

/-- Scalar multiplication adds the orders of compatible filtrations. -/
theorem smul_mem {a b : ℕ} {r : R} {x : M}
    (hr : r ∈ F.ideal a) (hx : x ∈ G.submodule b) :
    r • x ∈ G.submodule (a + b) := by
  have hr' : r ∈ F.orderDual (OrderDual.toDual a) := by simpa using hr
  have hx' : x ∈ G.filtration (OrderDual.toDual b) := by simpa using hx
  rw [← G.filtration_toDual (a + b)]
  exact SetLike.GradedSMul.smul_mem hr' hx'

/-- The scalar ideal at order `k + 1` annihilates the order-`k` module quotient. -/
theorem quotient_isTorsionBySet (k : ℕ) :
    Module.IsTorsionBySet R (G.quotient k) (F.ideal (k + 1)) := by
  apply (Module.isTorsionBySet_quotient_iff _ _).mpr
  intro x r hr
  simpa using smul_mem F G hr (by simp : x ∈ G.submodule 0)

/-- Each finite-order module quotient is a module over the matching ring quotient. -/
instance quotientModule (k : ℕ) : Module (R ⧸ F.ideal (k + 1)) (G.quotient k) :=
  (quotient_isTorsionBySet F G k).module

/-- A scalar represented by `r` acts by the original scalar multiplication. -/
@[simp]
theorem quotient_mk_smul (k : ℕ) (r : R) (x : G.quotient k) :
    Ideal.Quotient.mk (F.ideal (k + 1)) r • x = r • x :=
  Module.IsTorsionBySet.mk_smul (quotient_isTorsionBySet F G k) r x

/-- Ring and module quotient transitions commute with scalar multiplication. -/
@[simp]
theorem transition_smul {k l : ℕ} (h : k ≤ l)
    (r : R ⧸ F.ideal (l + 1)) (x : G.quotient l) :
    G.transition h (r • x) =
      Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) r •
        G.transition h x := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  simp only [quotient_mk_smul, Ideal.Quotient.factor_mk, map_smul]

/-- Scalar multiplication of completed rings and modules is computed componentwise. -/
instance completionSMul : SMul F.completion G.completion where
  smul r x :=
    ⟨fun k => F.projection k.unop r • G.projection k.unop x,
      (G.mem_completionSubmodule_iff _).mpr (by
        intro k l h
        rw [transition_smul F G h, F.factor_projection h, G.transition_projection h])⟩

/-- Projection of the completed action is the finite-order quotient action. -/
@[simp]
theorem projection_smul (k : ℕ) (r : F.completion) (x : G.completion) :
    G.projection k (r • x) = F.projection k r • G.projection k x :=
  G.projection_mk _ _ k

/-- The completed module is a module over the completed ring. -/
instance completionModule : Module F.completion G.completion where
  one_smul x := by ext k; simp
  mul_smul r s x := by ext k; simp [mul_smul]
  smul_zero r := by ext k; simp
  smul_add r x y := by ext k; simp [smul_add]
  add_smul r s x := by ext k; simp [add_smul]
  zero_smul x := by ext k; simp

/-- The canonical scalar map extends the original action on the completion. -/
@[simp]
theorem toCompletion_smul (r : R) (x : G.completion) :
    F.toCompletion r • x = r • x := by
  apply G.completion_ext
  intro k
  simp

/-- The canonical module map intertwines scalar multiplication. -/
theorem of_smul (r : R) (x : M) :
    G.of (r • x) = F.toCompletion r • G.of x := by
  rw [toCompletion_smul, map_smul]

/-- A scalar vanishing to order `a` and a vector vanishing to order `b`
have product vanishing to order `a + b`. -/
theorem smul_mem_completedFiltration {a b : ℕ} {r : F.completion} {x : G.completion}
    (hr : r ∈ F.completionIdeal a) (hx : x ∈ G.completedFiltration.submodule b) :
    r • x ∈ G.completedFiltration.submodule (a + b) := by
  cases a with
  | zero =>
    cases b with
    | zero => simp
    | succ b =>
      rw [Nat.zero_add, completedFiltration_succ, LinearMap.mem_ker, projection_smul]
      rw [completedFiltration_succ, LinearMap.mem_ker] at hx
      rw [hx, smul_zero]
  | succ a =>
    have hab : a + 1 + b = (a + b) + 1 := by omega
    rw [hab, completedFiltration_succ, LinearMap.mem_ker, projection_smul]
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (F.projection (a + b) r)
    obtain ⟨y, hy⟩ := (G.submodule (a + b + 1)).mkQ_surjective (G.projection (a + b) x)
    have hsr : s ∈ F.ideal (a + 1) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have he := congrArg (Ideal.Quotient.factor
        (F.antitone (Nat.add_le_add_right (Nat.le_add_right a b) 1))) hs
      rw [Ideal.Quotient.factor_mk, F.factor_projection (Nat.le_add_right a b)] at he
      rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker] at hr
      exact he.trans hr
    have hyx : y ∈ G.submodule b := by
      cases b with
      | zero => simp
      | succ b =>
        apply (Submodule.Quotient.mk_eq_zero _).mp
        have he := congrArg (G.transition (by omega : b ≤ a + (b + 1))) hy
        rw [Submodule.mkQ_apply, G.transition_mk, G.transition_projection] at he
        rw [completedFiltration_succ, LinearMap.mem_ker] at hx
        exact he.trans hx
    rw [← hs, ← hy, quotient_mk_smul, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    simpa only [hab] using smul_mem F G hsr hyx

/-- The induced filtration as submodules over the completed scalar ring. -/
def completedScalarFiltration : ModuleFiltration F.completion G.completion where
  submodule k :=
    { __ := (G.completedFiltration.submodule k).toAddSubmonoid
      smul_mem' r x hx := by
        simpa using smul_mem_completedFiltration F G
          (by simp : r ∈ F.completionIdeal 0) hx }
  antitone := fun _ _ h => G.completedFiltration.antitone h
  zero_eq_top := by
    ext x
    exact Iff.trans (by rfl) (by simp)

/-- Completing the scalars preserves the induced filtration sets. -/
@[simp]
theorem mem_completedScalarFiltration_iff (k : ℕ) (x : G.completion) :
    x ∈ (completedScalarFiltration F G).submodule k ↔
      x ∈ G.completedFiltration.submodule k := (Iff.rfl)

/-- The induced filtrations remain compatible under completed scalar multiplication. -/
instance completionIsModuleFiltration :
    IsModuleFiltration F.completionFiltration.orderDual
      (fun k => F.completionFiltration.ideal (k.ofDual + 1))
      (completedScalarFiltration F G).filtration
      (fun k => (completedScalarFiltration F G).submodule (k.ofDual + 1)) where
  smul_mem {a b r x} hr hx := by
    simp only [AlgFiltration.orderDual_apply, AlgFiltration.completionFiltration_ideal] at hr
    rw [← OrderDual.toDual_ofDual b,
      (completedScalarFiltration F G).filtration_toDual, mem_completedScalarFiltration_iff] at hx
    rw [← OrderDual.toDual_ofDual (a +ᵥ b),
      (completedScalarFiltration F G).filtration_toDual, mem_completedScalarFiltration_iff]
    exact smul_mem_completedFiltration F G hr hx

end Mei.ModuleFiltration
