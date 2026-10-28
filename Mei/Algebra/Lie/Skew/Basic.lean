/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Derivation
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The Lie algebra of an alternating lattice form

An alternating form `β` defines the bracket `[X_n, X_m] = β(m,n) X_(n+m)`
on the free coefficient module on an abelian group. The construction retains
all generators, including those in the radical of the form. Its action on the
monoid algebra sends `X_n(z^p)` to `β(p,n) z^(n+p)`; this action can have a kernel.

The bracket convention follows Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1, arXiv:1411.1394v2. The coefficient action is Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(ii), arXiv:1503.06183v5. The finite-sum presentation follows
`Mei.LogarithmicVectorField`, using Mathlib's `Finsupp.lsum` to extend bilinear
generator formulas and the existing monomial logarithmic derivations for the action.
-/

public section

noncomputable section

namespace Mei

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]

/-- The free module on the exponent group, with the Lie bracket determined by an
alternating form. Radical degrees remain independent generators. -/
def SkewLieAlgebra (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (_hβ : β.IsAlt) := Γ →₀ R

namespace SkewLieAlgebra

variable (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt)

instance : AddCommGroup (SkewLieAlgebra β hβ) := inferInstanceAs (AddCommGroup (Γ →₀ R))
instance {S : Type*} [Semiring S] [Module S R] : Module S (SkewLieAlgebra β hβ) :=
  inferInstanceAs (Module S (Γ →₀ R))

instance {S : Type*} [CommRing S] [Algebra S R] :
    IsScalarTower S R (SkewLieAlgebra β hβ) :=
  inferInstanceAs (IsScalarTower S R (Γ →₀ R))

/-- The coefficient coordinates of a skew Lie element. -/
def toFinsupp : SkewLieAlgebra β hβ ≃ₗ[R] Γ →₀ R :=
  { toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The homogeneous inclusion `r ↦ r X_n`. -/
def single (n : Γ) : R →ₗ[R] SkewLieAlgebra β hβ :=
  (toFinsupp β hβ).symm.toLinearMap.comp (Finsupp.lsingle n)

/-- The homogeneous inclusion in coefficient coordinates. -/
theorem single_def (n : Γ) :
    single β hβ n = (toFinsupp β hβ).symm.toLinearMap.comp (Finsupp.lsingle n) := (rfl)

@[simp]
theorem toFinsupp_single (n : Γ) (r : R) :
    toFinsupp β hβ (single β hβ n r) = Finsupp.single n r := (rfl)

/-- A homogeneous skew generator vanishes exactly when its coefficient does. -/
@[simp]
theorem single_eq_zero (n : Γ) (r : R) : single β hβ n r = 0 ↔ r = 0 := by
  rw [← (toFinsupp β hβ).map_eq_zero_iff, toFinsupp_single, Finsupp.single_eq_zero]

/-- Equality is detected by all exponent coefficients. -/
@[ext]
theorem ext {x y : SkewLieAlgebra β hβ}
    (h : ∀ n, toFinsupp β hβ x n = toFinsupp β hβ y n) : x = y :=
  (toFinsupp β hβ).injective (Finsupp.ext h)

/-- Induction on finite sums of homogeneous skew generators. -/
@[elab_as_elim]
theorem induction_on {P : SkewLieAlgebra β hβ → Prop} (x : SkewLieAlgebra β hβ)
    (h0 : P 0) (hs : ∀ n r, P (single β hβ n r))
    (ha : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using Finsupp.induction_linear with
  | zero => exact h0
  | single n r => exact hs n r
  | add x y hx hy => exact ha x y hx hy

noncomputable instance : Bracket (SkewLieAlgebra β hβ) (SkewLieAlgebra β hβ) :=
  ⟨fun x y => (Finsupp.lsum R fun n =>
      (Finsupp.lsum R fun m =>
        ((LinearMap.mul R R).compr₂
          ((single β hβ (n + m)).comp (LinearMap.mulRight R (β m n)))).flip).flip)
        (toFinsupp β hβ x) (toFinsupp β hβ y)⟩

private theorem bracket_def (x y : SkewLieAlgebra β hβ) :
    ⁅x, y⁆ = (Finsupp.lsum R fun n =>
      (Finsupp.lsum R fun m =>
        ((LinearMap.mul R R).compr₂
          ((single β hβ (n + m)).comp (LinearMap.mulRight R (β m n)))).flip).flip)
        (toFinsupp β hβ x) (toFinsupp β hβ y) := (rfl)

/-- The alternating-form bracket on homogeneous generators. -/
@[simp]
theorem single_bracket_single (n m : Γ) (r s : R) :
    ⁅single β hβ n r, single β hβ m s⁆ =
      single β hβ (n + m) (r * s * β m n) := by
  simp [bracket_def, Finsupp.lsum_single]

private theorem bracket_add_left (x y z : SkewLieAlgebra β hβ) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by simp only [bracket_def, map_add, LinearMap.add_apply]

private theorem bracket_add_right (x y z : SkewLieAlgebra β hβ) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by simp only [bracket_def, map_add]

private theorem bracket_swap (x y : SkewLieAlgebra β hβ) : ⁅x, y⁆ = -⁅y, x⁆ := by
  induction x using induction_on β hβ with
  | h0 => simp [bracket_def]
  | hs n r =>
    induction y using induction_on β hβ with
    | h0 => simp [bracket_def]
    | hs m s =>
      simp only [single_bracket_single, ← hβ.neg n m, add_comm m n]
      rw [← (single β hβ (n + m)).map_neg]
      congr 1
      ring
    | ha y z hy hz => simp [bracket_add_left, bracket_add_right, hy, hz, add_comm]
  | ha x z hx hz => simp [bracket_add_left, bracket_add_right, hx, hz, add_comm]

instance : LieRing (SkewLieAlgebra β hβ) where
  add_lie := by exact bracket_add_left β hβ
  lie_add := by exact bracket_add_right β hβ
  lie_self x := by
    induction x using induction_on β hβ with
    | h0 => simp [bracket_def]
    | hs n r => simp [hβ.self_eq_zero]
    | ha x y hx hy =>
      simp only [bracket_add_left, bracket_add_right, hx, hy, zero_add, add_zero]
      rw [bracket_swap β hβ x y, add_neg_cancel]
  leibniz_lie x y z := by
    induction x using induction_on β hβ with
    | h0 => simp [bracket_def]
    | hs n r =>
      induction y using induction_on β hβ with
      | h0 => simp [bracket_def]
      | hs m s =>
        induction z using induction_on β hβ with
        | h0 => simp [bracket_def]
        | hs p t =>
          simp only [single_bracket_single, add_assoc, add_left_comm m n p]
          rw [← (single β hβ (n + (m + p))).map_add]
          congr 1
          simp only [map_add, LinearMap.add_apply, ← hβ.neg n m]
          ring
        | ha z w hz hw =>
          simp only [bracket_add_right, hz, hw]
          abel
      | ha y w hy hw =>
        simp only [bracket_add_left, bracket_add_right, hy, hw]
        abel
    | ha x w hx hw =>
      simp only [bracket_add_left, bracket_add_right, hx, hw]
      abel

instance : LieAlgebra R (SkewLieAlgebra β hβ) where
  lie_smul r x y := by simp only [bracket_def, map_smul]

/-- Restricting coefficient scalars retains the skew Lie algebra. -/
instance {S : Type*} [CommRing S] [Algebra S R] :
    LieAlgebra S (SkewLieAlgebra β hβ) where
  lie_smul s x y := by
    simpa only [IsScalarTower.algebraMap_smul] using
      lie_smul (algebraMap S R s) x y

/-- Generators on the same integer ray commute, without any nondegeneracy assumption. -/
theorem single_zsmul_bracket_single_zsmul (w : Γ) (a b : ℤ) (r s : R) :
    ⁅single β hβ (a • w) r, single β hβ (b • w) s⁆ = 0 := by
  simp [single_bracket_single, hβ.self_eq_zero]

private def actionLinear : SkewLieAlgebra β hβ →ₗ[R]
    Derivation R (_root_.AddMonoidAlgebra R Γ) (_root_.AddMonoidAlgebra R Γ) :=
  (Finsupp.lsum R fun n => LinearMap.toSpanSingleton R _
    (AddMonoidAlgebra.monomialDerivation n (β.flip n).toAddMonoidHom)).comp
      (toFinsupp β hβ).toLinearMap

private theorem actionLinear_single (n : Γ) (r : R) :
    actionLinear β hβ (single β hβ n r) =
      r • AddMonoidAlgebra.monomialDerivation n (β.flip n).toAddMonoidHom := by
  simp only [actionLinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    toFinsupp_single, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The Poisson action of skew generators on monoid coefficients. It need not be
faithful: generators in the radical act by zero. -/
def action : SkewLieAlgebra β hβ →ₗ⁅R⁆
    Derivation R (_root_.AddMonoidAlgebra R Γ) (_root_.AddMonoidAlgebra R Γ) :=
  { actionLinear β hβ with
    map_lie' := by
      intro x y
      simp only [LinearMap.toFun_eq_coe]
      induction x using induction_on β hβ with
      | h0 => simp
      | hs n r =>
        induction y using induction_on β hβ with
        | h0 => simp
        | hs m s =>
          rw [single_bracket_single, actionLinear_single, actionLinear_single,
            actionLinear_single]
          rw [← (AddMonoidAlgebra.monomialDerivation (R := R) n).map_smul,
            ← (AddMonoidAlgebra.monomialDerivation (R := R) m).map_smul,
            AddMonoidAlgebra.lie_monomialDerivation,
            ← (AddMonoidAlgebra.monomialDerivation (R := R) (n + m)).map_smul]
          congr 1
          ext p
          simp only [AddMonoidHom.smul_apply, AddMonoidHom.sub_apply,
            LinearMap.toAddMonoidHom_coe, LinearMap.flip_apply, smul_eq_mul,
            map_add, LinearMap.add_apply]
          rw [← hβ.neg n m]
          ring
        | ha y z hy hz => simp_all
      | ha x z hx hz => simp_all }

/-- The action of one generator is its monomial logarithmic derivation. -/
@[simp]
theorem action_single (n : Γ) (r : R) :
    action β hβ (single β hβ n r) =
      r • AddMonoidAlgebra.monomialDerivation n (β.flip n).toAddMonoidHom :=
  actionLinear_single β hβ n r

/-- The skew Poisson formula on a coefficient monomial. -/
theorem action_single_apply (n p : Γ) (r s : R) :
    action β hβ (single β hβ n r) (_root_.AddMonoidAlgebra.single p s) =
      _root_.AddMonoidAlgebra.single (n + p) (r * s * β p n) := by
  simp [mul_assoc]

end SkewLieAlgebra
end Mei
