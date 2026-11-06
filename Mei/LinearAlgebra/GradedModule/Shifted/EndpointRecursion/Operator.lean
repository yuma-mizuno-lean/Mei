/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion
public import Mei.LinearAlgebra.End.Recursion
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Lower-degree recursions with variable incoming coefficients

The lower-degree endpoint operator acts on linear families of homogeneous
coefficients by postcomposition. Evaluating such a family at any input
intertwines the operators, their iterates and their finite recursion solutions.
In particular the operator-valued recursion has a unique solution, and
pointwise coefficient equations characterize it without a finite-generation
hypothesis on the input module.

The construction uses Mathlib's `LinearEquiv.linearMapPi` and
`LinearMap.llcomp`, and the shared nilpotent recursion theorem
`Module.End.comp_finiteRecursion`. It supplies the linear-family version of
the backward-ray method in Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M H V : Type*} [AddCommGroup Γ] [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid H] [Module R H]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ) (k : ℕ)

/-- An endpoint function whose homogeneous coefficients depend linearly on an
arbitrary incoming module. -/
abbrev ShiftedEndpointOperator := V → (n : d.cutoff k) → H →ₗ[R] ℳ (p + n.val)

/-- Linear families of endpoint coefficients are linear maps into the endpoint
function module. Neither the endpoint type nor the input module need be finite. -/
def shiftedEndpointOperatorEquiv :
    ShiftedEndpointOperator (H := H) (V := V) d ℳ p k ≃ₗ[R]
      (H →ₗ[R] ShiftedEndpointFunction d ℳ p V k) :=
  (LinearEquiv.piCongrRight fun _ : V => LinearEquiv.linearMapPi R).trans
    (LinearEquiv.linearMapPi R)

@[simp]
theorem shiftedEndpointOperatorEquiv_apply
    (F : ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) (x : H) (Q : V)
    (n : d.cutoff k) :
    shiftedEndpointOperatorEquiv d ℳ p k F x Q n = F Q n x := (rfl)

@[simp]
theorem shiftedEndpointOperatorEquiv_symm_apply
    (F : H →ₗ[R] ShiftedEndpointFunction d ℳ p V k) (Q : V) (n : d.cutoff k) (x : H) :
    (shiftedEndpointOperatorEquiv d ℳ p k).symm F Q n x = F x Q n := (rfl)

/-- Evaluation of every endpoint coefficient at one incoming input. -/
def shiftedEndpointEval (x : H) :
    ShiftedEndpointOperator (H := H) (V := V) d ℳ p k →ₗ[R]
      ShiftedEndpointFunction d ℳ p V k :=
  (LinearMap.applyₗ (R := R) x).comp (shiftedEndpointOperatorEquiv d ℳ p k).toLinearMap

@[simp]
theorem shiftedEndpointEval_apply (x : H)
    (F : ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) (Q : V) (n : d.cutoff k) :
    shiftedEndpointEval d ℳ p k x F Q n = F Q n x := (rfl)

variable {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
  (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
  (point : ι → V → (n m : d.cutoff k) → V)

local notation "U" => (shiftedLowerStep d ℳ p k events block point :
  Module.End R (ShiftedEndpointFunction d ℳ p V k))
local notation "e" => shiftedEndpointOperatorEquiv (H := H) (V := V) d ℳ p k

/-- The lower-degree step on linear families, transported from postcomposition
by the coefficient step. Its blocks are postcomposition by the original blocks. -/
def shiftedOperatorLowerStep :
    Module.End R (ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) :=
  (e).symm.toLinearMap.comp ((LinearMap.llcomp R H _ _ U).comp (e).toLinearMap)

local notation "Uop" => shiftedOperatorLowerStep (H := H) d ℳ p k events block point

/-- Evaluation intertwines the operator-valued and coefficient-valued steps. -/
@[simp]
theorem shiftedEndpointEval_shiftedOperatorLowerStep (x : H)
    (F : ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) :
    shiftedEndpointEval d ℳ p k x (Uop F) = U (shiftedEndpointEval d ℳ p k x F) := by
  simp [shiftedOperatorLowerStep, shiftedEndpointEval]

/-- Each operator coefficient is the finite sum of composed homogeneous blocks.
Zero blocks and inputs remain in this identity of linear maps. -/
theorem shiftedOperatorLowerStep_apply
    (F : ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) (Q : V) (n : d.cutoff k) :
    Uop F Q n = ∑ b ∈ events Q n, ∑ m : d.cutoff k,
      if h : d.Precedes m.val n.val then
        (block b n m h).comp (F (point b Q n m) m) else 0 := by
  classical
  apply LinearMap.ext
  intro x
  have he := congrFun (congrFun
    (shiftedEndpointEval_shiftedOperatorLowerStep d ℳ p k events block point x F) Q) n
  simp only [shiftedEndpointEval_apply] at he
  rw [shiftedLowerStep_apply] at he
  rw [he]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> rfl

/-- Evaluation commutes with every iterate, including the zeroth iterate. -/
@[simp]
theorem shiftedEndpointEval_shiftedOperatorLowerStep_pow (j : ℕ) (x : H)
    (F : ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) :
    shiftedEndpointEval d ℳ p k x ((Uop ^ j) F) =
      (U ^ j) (shiftedEndpointEval d ℳ p k x F) := by
  exact (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute
    (f := shiftedEndpointEval d ℳ p k x) (g := Uop) (g₂ := U)
    (LinearMap.ext fun F => (shiftedEndpointEval_shiftedOperatorLowerStep
      d ℳ p k events block point x F).symm) j) F).symm

/-- The operator-valued step has the same nilpotency bound as the coefficient
step, even for infinitely generated incoming modules. -/
theorem shiftedOperatorLowerStep_pow_eq_zero : Uop ^ (k + 1) = 0 := by
  ext F Q n x
  have he := congrFun (congrFun
    (shiftedEndpointEval_shiftedOperatorLowerStep_pow d ℳ p k events block point
      (k + 1) x F) Q) n
  simpa [shiftedLowerStep_pow_eq_zero] using he

/-- Evaluating the unique finite operator solution gives the unique finite
coefficient solution for that input. -/
@[simp]
theorem shiftedEndpointEval_finiteRecursion (x : H)
    (F : ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) :
    shiftedEndpointEval d ℳ p k x (((Uop).finiteRecursion (k + 1)) F) =
      Module.End.finiteRecursion U (k + 1) (shiftedEndpointEval d ℳ p k x F) := by
  exact LinearMap.congr_fun (Module.End.comp_finiteRecursion Uop U
    (shiftedEndpointEval d ℳ p k x)
    (LinearMap.ext (shiftedEndpointEval_shiftedOperatorLowerStep
      d ℳ p k events block point x))
    (shiftedOperatorLowerStep_pow_eq_zero d ℳ p k events block point)
    (shiftedLowerStep_pow_eq_zero d ℳ p k events block point)) F

/-- Pointwise recursions for every input are equivalent to the single equation
of linear families; their common solution is the finite operator recursion. -/
theorem eq_finiteRecursion_iff_forall_eval_eq_add
    (source F : ShiftedEndpointOperator (H := H) (V := V) d ℳ p k) :
    F = (Uop).finiteRecursion (k + 1) source ↔
      ∀ x : H, shiftedEndpointEval d ℳ p k x F =
        shiftedEndpointEval d ℳ p k x source + U (shiftedEndpointEval d ℳ p k x F) := by
  constructor
  · rintro rfl x
    rw [shiftedEndpointEval_finiteRecursion]
    exact Module.End.finiteRecursion_eq_add U
      (shiftedLowerStep_pow_eq_zero d ℳ p k events block point) _
  · intro hF
    apply (Uop).eq_finiteRecursion_of_eq_add
      (shiftedOperatorLowerStep_pow_eq_zero d ℳ p k events block point)
    funext Q n
    apply LinearMap.ext
    intro x
    have he := congrFun (congrFun (hF x) Q) n
    simpa only [Pi.add_apply, shiftedEndpointEval_apply, LinearMap.add_apply,
      ← shiftedEndpointEval_shiftedOperatorLowerStep] using he

end Mei.PositiveDegrees
