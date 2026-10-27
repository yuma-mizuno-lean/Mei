/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Derivation
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Formal logarithmic vector fields

For an additive map `ρ : Γ →+ Λ`, a formal logarithmic vector field is a finite
sum of symbols `z^n ∂_m`, where `m : Λ →+ R`. Its bracket has degree `n + n'`
and character `m(ρ(n')) m' - m'(ρ(n)) m`. The construction retains the full
character even when `ρ` has a kernel or its image does not span the tangent lattice.

The Jacobi identity is inherited from a faithful realization as derivations of
`R[Γ × Λ]`: use exponent `(n, ρ(n))` and the character on the second factor.
The ordinary action on `R[Γ]` need not be faithful. These constructions use
`Mei.AddMonoidAlgebra.monomialDerivation` and Mathlib's `Finsupp.lsum`.
The logarithmic-vector-field bracket follows Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

open _root_.AddMonoidAlgebra

namespace Mei

variable (R Γ Λ : Type*) [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]

/-- Finite formal sums of degree-indexed additive characters. The spatial map is
part of the type because it determines the Lie bracket. -/
def LogarithmicVectorField (_ρ : Γ →+ Λ) := Γ →₀ (Λ →+ R)

namespace LogarithmicVectorField

variable {R Γ Λ} (ρ : Γ →+ Λ)

instance : AddCommGroup (LogarithmicVectorField R Γ Λ ρ) :=
  inferInstanceAs (AddCommGroup (Γ →₀ (Λ →+ R)))

instance : Module R (LogarithmicVectorField R Γ Λ ρ) :=
  inferInstanceAs (Module R (Γ →₀ (Λ →+ R)))

/-- The coefficient description of formal logarithmic vector fields. -/
def toFinsupp : LogarithmicVectorField R Γ Λ ρ ≃ₗ[R] Γ →₀ (Λ →+ R) :=
  { toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- A homogeneous formal vector field `z^n ∂_m`, linear in its character. -/
def single (n : Γ) : (Λ →+ R) →ₗ[R] LogarithmicVectorField R Γ Λ ρ :=
  (toFinsupp ρ).symm.toLinearMap.comp (Finsupp.lsingle n)

/-- The homogeneous inclusion is the finitely supported singleton in coefficient coordinates. -/
theorem single_def (n : Γ) :
    single (R := R) ρ n = (toFinsupp ρ).symm.toLinearMap.comp (Finsupp.lsingle n) := (rfl)

/-- The coefficients of a homogeneous formal vector field. -/
@[simp]
theorem toFinsupp_single (n : Γ) (m : Λ →+ R) :
    toFinsupp ρ (single ρ n m) = Finsupp.single n m := (rfl)

/-- The character of a homogeneous formal vector field is unique. -/
theorem single_injective (n : Γ) : Function.Injective (single (R := R) ρ n) := by
  intro m m' h
  apply Finsupp.single_injective n
  simpa only [toFinsupp_single] using congrArg (toFinsupp ρ) h

/-- Equality of formal vector fields is equality of their characters in every degree. -/
@[ext]
theorem ext {x y : LogarithmicVectorField R Γ Λ ρ}
    (h : ∀ n, toFinsupp ρ x n = toFinsupp ρ y n) : x = y :=
  (toFinsupp ρ).injective (Finsupp.ext h)

/-- Prove an additive property by checking homogeneous formal vector fields. -/
@[elab_as_elim]
theorem induction_on {P : LogarithmicVectorField R Γ Λ ρ → Prop}
    (x : LogarithmicVectorField R Γ Λ ρ) (h0 : P 0)
    (hs : ∀ n m, P (single ρ n m))
    (ha : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using Finsupp.induction_linear with
  | zero => exact h0
  | single n m => exact hs n m
  | add x y hx hy => exact ha x y hx hy

noncomputable instance : Bracket (LogarithmicVectorField R Γ Λ ρ)
    (LogarithmicVectorField R Γ Λ ρ) :=
  ⟨fun x y => (Finsupp.lsum R fun n =>
    (Finsupp.lsum R fun n' =>
      ((LinearMap.mk₂ R (fun m m' : Λ →+ R => m (ρ n') • m' - m' (ρ n) • m)
        (by intros; ext; simp; ring)
        (by intros; ext; simp; ring)
        (by intros; ext; simp; ring)
        (by intros; ext; simp; ring)).compr₂ (single ρ (n + n'))).flip).flip)
          (toFinsupp ρ x) (toFinsupp ρ y)⟩

private theorem bracket_def (x y : LogarithmicVectorField R Γ Λ ρ) :
    ⁅x, y⁆ = (Finsupp.lsum R fun n =>
      (Finsupp.lsum R fun n' =>
        ((LinearMap.mk₂ R (fun m m' : Λ →+ R => m (ρ n') • m' - m' (ρ n) • m)
          (by intros; ext; simp; ring)
          (by intros; ext; simp; ring)
          (by intros; ext; simp; ring)
          (by intros; ext; simp; ring)).compr₂ (single ρ (n + n'))).flip).flip)
        (toFinsupp ρ x) (toFinsupp ρ y) := (rfl)

/-- The formal logarithmic-vector-field bracket on homogeneous generators. -/
@[simp]
theorem single_bracket_single (n n' : Γ) (m m' : Λ →+ R) :
    ⁅single ρ n m, single ρ n' m'⁆ =
      single ρ (n + n') (m (ρ n') • m' - m' (ρ n) • m) := by
  simp [bracket_def, Finsupp.lsum_single]

-- Precompose characters using the existing linear-map composition and coefficient equivalences.
private abbrev pullCharacter {M : Type*} [AddCommMonoid M] (f : M →+ Λ) :
    (Λ →+ R) →ₗ[R] (M →+ R) :=
  (addMonoidHomLequivNat R).symm.toLinearMap.comp
    ((LinearMap.lcomp R R f.toNatLinearMap).comp (addMonoidHomLequivNat R).toLinearMap)

/-- A faithful realization on an enlarged monoid algebra. The extra tangent variables
retain characters invisible to the ordinary coefficient action. -/
def realization : LogarithmicVectorField R Γ Λ ρ →ₗ[R]
    Derivation R R[Γ × Λ] R[Γ × Λ] :=
  (Finsupp.lsum R fun n =>
    (AddMonoidAlgebra.monomialDerivation (n, ρ n)).comp
      (pullCharacter (AddMonoidHom.snd Γ Λ))).comp (toFinsupp ρ).toLinearMap

/-- The faithful realization uses the graph exponent and the second-factor character. -/
@[simp]
theorem realization_single (n : Γ) (m : Λ →+ R) :
    realization ρ (single ρ n m) =
      AddMonoidAlgebra.monomialDerivation (n, ρ n) (m.comp (AddMonoidHom.snd Γ Λ)) := by
  simp only [realization, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    toFinsupp_single, Finsupp.lsum_single]
  congr 1

/-- Recover any formal coefficient from the faithful action on a tangent monomial. -/
theorem realization_coeff (x : LogarithmicVectorField R Γ Λ ρ) (n : Γ) (l : Λ) :
    (realization ρ x (_root_.AddMonoidAlgebra.single (0, l) 1)).coeff (n, ρ n + l) =
      toFinsupp ρ x n l := by
  induction x using induction_on ρ with
  | h0 => simp
  | hs n' m =>
    simp only [realization_single, AddMonoidAlgebra.monomialDerivation_single,
      AddMonoidHom.comp_apply, one_mul, Prod.mk_add_mk,
      add_zero, toFinsupp_single]
    by_cases h : n' = n
    · subst n'; simp
    · simp [h]
  | ha x y hx hy => simp [hx, hy]

/-- Formal characters are not quotiented by the kernel of the spatial action. -/
theorem realization_injective : Function.Injective (realization (R := R) ρ) := by
  intro x y h
  ext n l
  have he := congrArg (fun D : Derivation R R[Γ × Λ] R[Γ × Λ] =>
    (D (_root_.AddMonoidAlgebra.single (0, l) 1)).coeff (n, ρ n + l)) h
  simpa only [realization_coeff] using he

/-- The faithful realization preserves the logarithmic Lie bracket. -/
theorem realization_bracket (x y : LogarithmicVectorField R Γ Λ ρ) :
    realization ρ ⁅x, y⁆ = ⁅realization ρ x, realization ρ y⁆ := by
  induction x using induction_on ρ with
  | h0 => ext a; simp [bracket_def, Derivation.commutator_apply]
  | hs n m =>
    induction y using induction_on ρ with
    | h0 => ext a; simp [bracket_def, Derivation.commutator_apply]
    | hs n' m' =>
      rw [single_bracket_single, realization_single, realization_single,
        realization_single, AddMonoidAlgebra.lie_monomialDerivation]
      congr 1; simp
    | ha y z hy hz =>
      simpa only [bracket_def, map_add, LinearMap.add_apply, LieRing.lie_add] using
        congrArg₂ (· + ·) hy hz
  | ha x z hx hz =>
    simpa only [bracket_def, map_add, LinearMap.add_apply, LieRing.add_lie] using
      congrArg₂ (· + ·) hx hz

instance : LieRing (LogarithmicVectorField R Γ Λ ρ) where
  add_lie x y z := by simp [bracket_def, map_add]
  lie_add x y z := by simp [bracket_def, map_add]
  lie_self x := by
    apply realization_injective ρ
    simp only [realization_bracket, lie_self, map_zero]
  leibniz_lie x y z := by
    apply realization_injective ρ
    simpa only [realization_bracket, map_add] using
      LieRing.leibniz_lie (realization ρ x) (realization ρ y) (realization ρ z)

instance : LieAlgebra R (LogarithmicVectorField R Γ Λ ρ) where
  lie_smul t x y := by simp [bracket_def, map_smul]

private def actionLinear : LogarithmicVectorField R Γ Λ ρ →ₗ[R]
    Derivation R R[Γ] R[Γ] :=
  (Finsupp.lsum R fun n =>
    (AddMonoidAlgebra.monomialDerivation n).comp (pullCharacter ρ)).comp
      (toFinsupp ρ).toLinearMap

private theorem actionLinear_single (n : Γ) (m : Λ →+ R) :
    actionLinear ρ (single ρ n m) =
      AddMonoidAlgebra.monomialDerivation n (m.comp ρ) := by
  simp only [actionLinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    toFinsupp_single, Finsupp.lsum_single]
  congr 1

/-- The ordinary coefficient action of a formal vector field. -/
def action : LogarithmicVectorField R Γ Λ ρ →ₗ⁅R⁆ Derivation R R[Γ] R[Γ] :=
  { actionLinear ρ with
    map_lie' := by
      intro x y
      simp only [LinearMap.toFun_eq_coe]
      induction x using induction_on ρ with
      | h0 => simp
      | hs n m =>
        induction y using induction_on ρ with
        | h0 => simp
        | hs n' m' =>
          rw [single_bracket_single, actionLinear_single, actionLinear_single,
            actionLinear_single, AddMonoidAlgebra.lie_monomialDerivation]
          congr 1
        | ha y z hy hz => simp_all
      | ha x z hx hz => simp_all }

/-- A homogeneous formal field acts as the logarithmic derivation obtained by
pulling its character back along the spatial map. -/
@[simp]
theorem action_single (n : Γ) (m : Λ →+ R) :
    action ρ (single ρ n m) = AddMonoidAlgebra.monomialDerivation n (m.comp ρ) :=
  actionLinear_single ρ n m

/-- The ordinary action has the expected logarithmic monomial formula. -/
theorem action_single_apply (n : Γ) (m : Λ →+ R) (p : Γ) (r : R) :
    action ρ (single ρ n m) (_root_.AddMonoidAlgebra.single p r) =
      _root_.AddMonoidAlgebra.single (n + p) (r * m (ρ p)) := by
  simp

end LogarithmicVectorField
end Mei
