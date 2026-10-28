/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.FunctionWall.Exp
public import Mei.RingTheory.FilteredAlgebra.Action

/-!
# Function walls on completed coefficient algebras

Compatible weight-zero units in graded quotient algebras act on the coefficient
completion by algebra automorphisms. The action is computed at each finite order,
preserves the completion filtration, and multiplies an element of fixed normal
weight by the corresponding integer power of the completed wall function.
If the wall function is one at order zero, every finite action is the exponential
of its logarithmic normal derivation, with nilpotency bound `k + 1` at order `k`.

The quotient gradings need only be preserved by the transition maps; the
completion itself need not have an internal direct-sum grading. The construction
uses `AlgFiltration.completedAction` and the finite `GradedAlgebra.functionWallAction`,
including its naturality and exponential comparison. The function-wall formula
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.AlgFiltration

open Mei.GradedAlgebra CategoryTheory Opposite

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (F : AlgFiltration A)
  (𝒜 : ∀ k : ℕ, ℤ → Submodule R (A ⧸ F.ideal (k + 1)))
  [∀ k, GradedAlgebra (𝒜 k)]
  (h𝒜 : ∀ {k l : ℕ} (h : k ≤ l) {i : ℤ} {a : A ⧸ F.ideal (l + 1)},
    a ∈ 𝒜 l i →
      Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a ∈ 𝒜 k i)
  (f : ∀ k, (𝒜 k 0)ˣ)
  (hf : ∀ {k l : ℕ} (h : k ≤ l),
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (algebraMap (𝒜 l 0) _ (f l : 𝒜 l 0)) =
        algebraMap (𝒜 k 0) _ (f k : 𝒜 k 0))

include hf in
private theorem map_wallUnit {k l : ℕ} (h : k ≤ l) :
    Units.map (Ideal.Quotient.factor
        (F.antitone (Nat.add_le_add_right h 1))).toMonoidHom
      (Units.map (algebraMap (𝒜 l 0) _).toMonoidHom (f l)) =
        Units.map (algebraMap (𝒜 k 0) _).toMonoidHom (f k) :=
  Units.ext (hf h)

include hf in
private theorem compatible_inv {k l : ℕ} (h : k ≤ l) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (algebraMap (𝒜 l 0) _ ((f l)⁻¹ : (𝒜 l 0)ˣ)) =
        algebraMap (𝒜 k 0) _ ((f k)⁻¹ : (𝒜 k 0)ˣ) := by
  have he := congrArg (fun u => (u⁻¹).val) (F.map_wallUnit 𝒜 f hf h)
  simpa using he

/-- Assemble compatible weight-zero wall functions into a unit of the completion. -/
def completedWallFunction : F.completionˣ where
  val := ⟨fun k => algebraMap (𝒜 k.unop 0) _ (f k.unop : 𝒜 k.unop 0),
    (F.mem_completion_iff _).mpr hf⟩
  inv := ⟨fun k => algebraMap (𝒜 k.unop 0) _ ((f k.unop)⁻¹ : (𝒜 k.unop 0)ˣ),
    (F.mem_completion_iff _).mpr (F.compatible_inv 𝒜 f hf)⟩
  val_inv := F.completion_ext fun k => by
    rw [F.projection_apply, F.projection_apply]
    simpa only [map_mul, map_one, Subring.coe_mul, Subring.coe_one,
      Pi.mul_apply, Pi.one_apply, unop_op] using
      congrArg (algebraMap (𝒜 k 0) (A ⧸ F.ideal (k + 1))) (Units.mul_inv (f k))
  inv_val := F.completion_ext fun k => by
    rw [F.projection_apply, F.projection_apply]
    simpa only [map_mul, map_one, Subring.coe_mul, Subring.coe_one,
      Pi.mul_apply, Pi.one_apply, unop_op] using
      congrArg (algebraMap (𝒜 k 0) (A ⧸ F.ideal (k + 1))) (Units.inv_mul (f k))

/-- A completed wall function has the specified weight-zero finite-order value. -/
@[simp]
theorem projection_completedWallFunction (k : ℕ) :
    F.projection k (F.completedWallFunction 𝒜 f hf : F.completionˣ) =
      algebraMap (𝒜 k 0) _ (f k : 𝒜 k 0) := by
  rw [F.projection_apply]
  rfl

/-- The constant wall function one assembles to the identity unit. -/
@[simp]
theorem completedWallFunction_one :
    F.completedWallFunction 𝒜 (fun _ => 1) (by intro k l h; simp) = 1 := by
  apply Units.ext
  apply F.completion_ext
  intro k
  rw [F.projection_completedWallFunction 𝒜 (fun _ => 1) (by intro k l h; simp)]
  simp

/-- Multiplication of compatible wall functions commutes with completion. -/
theorem completedWallFunction_mul (g : ∀ k, (𝒜 k 0)ˣ)
    (hg : ∀ {k l : ℕ} (h : k ≤ l),
      Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (algebraMap (𝒜 l 0) _ (g l : 𝒜 l 0)) =
          algebraMap (𝒜 k 0) _ (g k : 𝒜 k 0)) :
    F.completedWallFunction 𝒜 (fun k => f k * g k)
        (by intro k l h; simp only [Units.val_mul, map_mul, hf h, hg h]) =
      F.completedWallFunction 𝒜 f hf * F.completedWallFunction 𝒜 g hg := by
  apply Units.ext
  apply F.completion_ext
  intro k
  rw [F.projection_completedWallFunction 𝒜 (fun k => f k * g k)
    (by intro k l h; simp only [Units.val_mul, map_mul, hf h, hg h])]
  simp

/-- Inverting compatible wall functions commutes with completion. -/
theorem completedWallFunction_inv :
    F.completedWallFunction 𝒜 (fun k => (f k)⁻¹) (by exact F.compatible_inv 𝒜 f hf) =
      (F.completedWallFunction 𝒜 f hf)⁻¹ := by
  apply Units.ext
  apply F.completion_ext
  intro k
  rw [F.projection_apply, F.projection_apply]
  rfl

private def wallTransition {k l : ℕ} (h : k ≤ l) : 𝒜 l →+*ᵍ 𝒜 k :=
  { Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) with
    map_mem := h𝒜 h }

private def wallGroupDiagram : ℕᵒᵖ ⥤ GrpCat where
  obj k := GrpCat.of ((𝒜 k.unop 0)ˣ)
  map h := GrpCat.ofHom
    (Units.map (F.wallTransition 𝒜 h𝒜 (leOfHom h.unop)).gradedZeroRingHom.toMonoidHom)
  map_id k := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro u
    apply Units.ext
    apply Subtype.ext
    exact DFunLike.congr_fun Ideal.Quotient.factor_eq (u.val : A ⧸ F.ideal (k.unop + 1))
  map_comp h h' := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro u
    apply Units.ext
    apply Subtype.ext
    exact (Ideal.Quotient.factor_comp_apply
      (F.antitone (Nat.add_le_add_right (leOfHom h.unop) 1))
      (F.antitone (Nat.add_le_add_right (leOfHom h'.unop) 1)) _).symm

private def wallLabel : completedGroup (F.wallGroupDiagram 𝒜 h𝒜) :=
  ⟨f, (mem_completedGroup_iff _ _).mpr fun _ _ h => Units.ext (Subtype.ext (hf h))⟩

private def wallRepresentation (k : ℕ) :
    (F.wallGroupDiagram 𝒜 h𝒜).obj (op k) →*
      ((A ⧸ F.ideal (k + 1)) ≃ₐ[R] (A ⧸ F.ideal (k + 1))) where
  toFun := functionWallAction (𝒜 k)
  map_one' := functionWallAction_one (𝒜 k)
  map_mul' := functionWallAction_mul (𝒜 k)

private theorem wallRepresentation_compatible {k l : ℕ} (h : k ≤ l)
    (u : (F.wallGroupDiagram 𝒜 h𝒜).obj (op l)) (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (F.wallRepresentation 𝒜 h𝒜 l u a) =
      F.wallRepresentation 𝒜 h𝒜 k ((F.wallGroupDiagram 𝒜 h𝒜).map (homOfLE h).op u)
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) :=
  map_functionWallAction (𝒜 l) (𝒜 k) (F.wallTransition 𝒜 h𝒜 h) u a

/-- The algebra automorphism of the coefficient completion defined by compatible
weight-zero function walls on its quotients. -/
def completedFunctionWallAction : F.completion ≃ₐ[R] F.completion :=
  F.completedAction (F.wallRepresentation 𝒜 h𝒜) (F.wallRepresentation_compatible 𝒜 h𝒜)
    (F.wallLabel 𝒜 h𝒜 f hf)

/-- The completed action is evaluated by the finite function-wall action at each order. -/
@[simp]
theorem projection_completedFunctionWallAction (k : ℕ) (x : F.completion) :
    F.projection k (F.completedFunctionWallAction 𝒜 h𝒜 f hf x) =
      functionWallAction (𝒜 k) (f k) (F.projection k x) := by
  rw [completedFunctionWallAction,
    F.projection_completedAction (F.wallRepresentation 𝒜 h𝒜)
      (F.wallRepresentation_compatible 𝒜 h𝒜),
    CompletedGroup.projection_apply]
  rfl

/-- The finite projection formula characterizes the completed automorphism uniquely. -/
theorem completedFunctionWallAction_unique (e : F.completion ≃ₐ[R] F.completion)
    (he : ∀ k x, F.projection k (e x) =
      functionWallAction (𝒜 k) (f k) (F.projection k x)) :
    e = F.completedFunctionWallAction 𝒜 h𝒜 f hf := by
  apply AlgEquiv.ext
  intro x
  exact F.completion_ext fun k => (he k x).trans
    (F.projection_completedFunctionWallAction 𝒜 h𝒜 f hf k x).symm

/-- The identity wall function acts identically on the completion. -/
@[simp]
theorem completedFunctionWallAction_one :
    F.completedFunctionWallAction 𝒜 h𝒜 (fun _ => 1) (by intro k l h; simp) =
      AlgEquiv.refl :=
  (F.completedAction (F.wallRepresentation 𝒜 h𝒜)
    (F.wallRepresentation_compatible 𝒜 h𝒜)).map_one

/-- Inverting every finite wall function inverts the completed action. -/
theorem completedFunctionWallAction_inv :
    F.completedFunctionWallAction 𝒜 h𝒜 (fun k => (f k)⁻¹)
        (by exact F.compatible_inv 𝒜 f hf) =
      (F.completedFunctionWallAction 𝒜 h𝒜 f hf).symm :=
  map_inv (F.completedAction (F.wallRepresentation 𝒜 h𝒜)
    (F.wallRepresentation_compatible 𝒜 h𝒜)) (F.wallLabel 𝒜 h𝒜 f hf)

/-- Multiplying compatible wall functions composes their completed actions. -/
theorem completedFunctionWallAction_mul (g : ∀ k, (𝒜 k 0)ˣ)
    (hg : ∀ {k l : ℕ} (h : k ≤ l),
      Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (algebraMap (𝒜 l 0) _ (g l : 𝒜 l 0)) =
          algebraMap (𝒜 k 0) _ (g k : 𝒜 k 0)) :
    F.completedFunctionWallAction 𝒜 h𝒜 (fun k => f k * g k)
        (by intro k l h; simp only [Units.val_mul, map_mul, hf h, hg h]) =
      (F.completedFunctionWallAction 𝒜 h𝒜 g hg).trans
        (F.completedFunctionWallAction 𝒜 h𝒜 f hf) :=
  (F.completedAction (F.wallRepresentation 𝒜 h𝒜)
    (F.wallRepresentation_compatible 𝒜 h𝒜)).map_mul
      (F.wallLabel 𝒜 h𝒜 f hf) (F.wallLabel 𝒜 h𝒜 g hg)

/-- Function walls preserve and reflect every order of the completion filtration. -/
@[simp]
theorem completedFunctionWallAction_mem_completionIdeal_iff (k : ℕ) (x : F.completion) :
    F.completedFunctionWallAction 𝒜 h𝒜 f hf x ∈ F.completionIdeal k ↔
      x ∈ F.completionIdeal k :=
  F.completedAction_mem_completionIdeal_iff (F.wallRepresentation 𝒜 h𝒜)
    (F.wallRepresentation_compatible 𝒜 h𝒜) (F.wallLabel 𝒜 h𝒜 f hf) x k

/-- On a completed element of fixed normal weight, the wall formula uses an
integer power of the completed wall function, including for negative weights. -/
theorem completedFunctionWallAction_apply_of_mem {i : ℤ} (x : F.completion)
    (hx : ∀ k, F.projection k x ∈ 𝒜 k i) :
    F.completedFunctionWallAction 𝒜 h𝒜 f hf x =
      x * (F.completedWallFunction 𝒜 f hf ^ i : F.completionˣ) := by
  apply F.completion_ext
  intro k
  rw [F.projection_completedFunctionWallAction,
    functionWallAction_apply_of_mem (𝒜 k) (f k) (hx k), map_mul]
  congr 1
  have he : Units.map (F.projection k).toMonoidHom (F.completedWallFunction 𝒜 f hf) =
      Units.map (algebraMap (𝒜 k 0) _).toMonoidHom (f k) :=
    Units.ext (F.projection_completedWallFunction 𝒜 f hf k)
  have hp := congrArg Units.val
    ((map_zpow (Units.map (F.projection k).toMonoidHom) _ i).trans
      ((congrArg (fun u => u ^ i) he).trans
        (map_zpow (Units.map (algebraMap (𝒜 k 0) (A ⧸ F.ideal (k + 1))).toMonoidHom) (f k) i).symm))
  exact hp.symm

section Exponential

variable (hf₀ : algebraMap (𝒜 0 0) (A ⧸ F.ideal 1) (f 0 : 𝒜 0 0) = 1)

include hf hf₀ in
/-- A wall function equal to one at order zero has the standard finite nilpotency bound. -/
theorem wallFunction_sub_one_pow_eq_zero (k : ℕ) :
    (algebraMap (𝒜 k 0) (A ⧸ F.ideal (k + 1)) (f k : 𝒜 k 0) - 1) ^ (k + 1) = 0 := by
  have hu : (F.completedWallFunction 𝒜 f hf : F.completionˣ).val - 1 ∈
      F.completionIdeal 1 := by
    simpa only [completionIdeal_succ, RingHom.mem_ker, map_sub, map_one,
      projection_completedWallFunction, sub_eq_zero] using hf₀
  simpa only [map_sub, map_one, projection_completedWallFunction] using
    F.projection_pow_eq_zero hu k

variable [Algebra ℚ A]

include hf₀ in
/-- The completed function wall is the levelwise exponential of its logarithmic
normal derivation. Equality at every order determines its value on arbitrary
completed coefficients, without a finite homogeneous support assumption. -/
theorem projection_completedFunctionWallAction_eq_exp (k : ℕ) (x : F.completion) :
    F.projection k (F.completedFunctionWallAction 𝒜 h𝒜 f hf x) =
      IsNilpotent.exp (functionWallDerivation (𝒜 k) (f k)).toLinearMap
        (F.projection k x) := by
  rw [F.projection_completedFunctionWallAction]
  exact LinearMap.congr_fun (functionWallAction_eq_exp (𝒜 k) (f k)
    ⟨k + 1, F.wallFunction_sub_one_pow_eq_zero 𝒜 f hf hf₀ k⟩) _

end Exponential

end Mei.AlgFiltration
