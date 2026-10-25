/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Ideal.TensorProduct
public import Mei.RingTheory.FilteredAlgebra.Basic

/-!
# Total-degree filtrations on tensor product algebras

For families of ideals `I` and `J`, the order-`k` tensor filtration is the sum of
the images of `I a ⊗ J b` with `k ≤ a + b`. It is decreasing and inherits
multiplicativity and two-sidedness from the factors. If both families start at
the whole algebra, so does the tensor filtration. Thus it supplies the quotient
tower for completed tensor products of filtered associative algebras.
`Mei.AlgFiltration.tensorProduct` bundles these terms as an `AlgFiltration`;
the two algebra inclusions preserve its filtration orders.

The construction uses `Ideal.tensorProduct`, whose underlying scalar submodule
is Mathlib's bilinear image of `TensorProduct.mk`. The multiplicative filtration
instance uses order-dual natural indices, so its strict term at `k` is order `k+1`.
-/

public section

open scoped TensorProduct

namespace Ideal

variable (R : Type*) {A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- The decreasing total-degree tensor filtration of two ideal families. -/
noncomputable def tensorFiltration (I : ℕ → Ideal A) (J : ℕ → Ideal B)
    (k : ℕ) : Ideal (A ⊗[R] B) :=
  ⨆ a, ⨆ b, ⨆ (_ : k ≤ a + b), (I a).tensorProduct R (J b)

/-- The total-degree filtration is the sum of the tensor images above the cutoff. -/
theorem tensorFiltration_def (I : ℕ → Ideal A) (J : ℕ → Ideal B) (k : ℕ) :
    tensorFiltration R I J k =
      ⨆ a, ⨆ b, ⨆ (_ : k ≤ a + b), (I a).tensorProduct R (J b) := (rfl)

/-- Restricting scalars recovers the sum of the tensor images as submodules. -/
@[simp]
theorem tensorFiltration_restrictScalars (I : ℕ → Ideal A) (J : ℕ → Ideal B) (k : ℕ) :
    (tensorFiltration R I J k).restrictScalars R =
      ⨆ a, ⨆ b, ⨆ (_ : k ≤ a + b),
        Submodule.map₂ (TensorProduct.mk R A B)
          ((I a).restrictScalars R) ((J b).restrictScalars R) := by
  simp only [tensorFiltration_def, Submodule.restrictScalars_iSup, tensorProduct_restrictScalars]

/-- A tensor image of sufficiently large total order lies in the tensor filtration. -/
theorem tensorProduct_le_tensorFiltration (I : ℕ → Ideal A) (J : ℕ → Ideal B)
    {a b k : ℕ} (h : k ≤ a + b) :
    (I a).tensorProduct R (J b) ≤ tensorFiltration R I J k :=
  le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le h le_rfl))

/-- Pure tensors belong at the sum of their factor orders, and at every smaller order. -/
theorem tmul_mem_tensorFiltration {I : ℕ → Ideal A} {J : ℕ → Ideal B}
    {a b k : ℕ} (h : k ≤ a + b) {x : A} {y : B} (hx : x ∈ I a) (hy : y ∈ J b) :
    x ⊗ₜ[R] y ∈ tensorFiltration R I J k :=
  tensorProduct_le_tensorFiltration R I J h (tmul_mem_tensorProduct R hx hy)

/-- Containment of the tensor filtration can be checked on pure tensors. -/
theorem tensorFiltration_le_iff (I : ℕ → Ideal A) (J : ℕ → Ideal B)
    (k : ℕ) (K : Ideal (A ⊗[R] B)) :
    tensorFiltration R I J k ≤ K ↔
      ∀ a b, k ≤ a + b → ∀ x ∈ I a, ∀ y ∈ J b, x ⊗ₜ[R] y ∈ K := by
  simp only [tensorFiltration_def, iSup_le_iff, tensorProduct_le_iff]

/-- The total-degree tensor filtration is decreasing, even for arbitrary ideal families. -/
theorem tensorFiltration_antitone (I : ℕ → Ideal A) (J : ℕ → Ideal B) :
    Antitone (tensorFiltration R I J) := by
  intro k l hkl
  refine (tensorFiltration_le_iff R I J l _).mpr ?_
  intro a b hab x hx y hy
  exact tmul_mem_tensorFiltration R (hkl.trans hab) hx hy

/-- Inclusion of both factor families induces inclusion of their tensor filtrations. -/
theorem tensorFiltration_mono {I I' : ℕ → Ideal A} {J J' : ℕ → Ideal B}
    (hI : ∀ a, I a ≤ I' a) (hJ : ∀ b, J b ≤ J' b) (k : ℕ) :
    tensorFiltration R I J k ≤ tensorFiltration R I' J' k := by
  refine (tensorFiltration_le_iff R I J k _).mpr ?_
  intro a b hab x hx y hy
  exact tmul_mem_tensorFiltration R hab (hI a hx) (hJ b hy)

/-- If both factor families start at the whole algebra, the tensor filtration does too. -/
@[simp]
theorem tensorFiltration_zero (I : ℕ → Ideal A) (J : ℕ → Ideal B)
    (hI : I 0 = ⊤) (hJ : J 0 = ⊤) : tensorFiltration R I J 0 = ⊤ := by
  apply top_unique
  simpa [hI, hJ] using tensorProduct_le_tensorFiltration R I J (a := 0) (b := 0) le_rfl

/-- Total-degree tensor filtrations of two-sided ideal families are two-sided. -/
instance tensorFiltration_isTwoSided (I : ℕ → Ideal A) (J : ℕ → Ideal B)
    [∀ a, (I a).IsTwoSided] [∀ b, (J b).IsTwoSided] (k : ℕ) :
    (tensorFiltration R I J k).IsTwoSided where
  mul_mem_of_left z hx := by
    have h : tensorFiltration R I J k ≤ (tensorFiltration R I J k).comap
        (LinearMap.mulRight (A ⊗[R] B) z) := by
      refine (tensorFiltration_le_iff R I J k _).mpr ?_
      intro a b hab x hx y hy
      exact tensorProduct_le_tensorFiltration R I J hab
        ((I a).tensorProduct R (J b) |>.mul_mem_right z (tmul_mem_tensorProduct R hx hy))
    exact h hx

/-- Multiplicative factor families give a multiplicative tensor filtration. -/
theorem tensorFiltration_mul_le (I : ℕ → Ideal A) (J : ℕ → Ideal B)
    (hI : ∀ a b, I a * I b ≤ I (a + b))
    (hJ : ∀ a b, J a * J b ≤ J (a + b)) (k l : ℕ) :
    tensorFiltration R I J k * tensorFiltration R I J l ≤ tensorFiltration R I J (k + l) := by
  simp only [tensorFiltration_def, iSup_mul, mul_iSup, iSup_le_iff]
  intro c d hcd a b hab
  exact (tensorProduct_mul_le R _ _ _ _).trans
    ((tensorProduct_mono R (hI a c) (hJ b d)).trans
      (tensorProduct_le_tensorFiltration R I J (by omega)))

/-- Multiplicative ideal families induce the standard ring filtration on dual natural indices. -/
instance tensorFiltration_isRingFiltration (I : ℕ → Ideal A) (J : ℕ → Ideal B)
    [SetLike.GradedMonoid (fun k : ℕᵒᵈ => I k.ofDual)]
    [SetLike.GradedMonoid (fun k : ℕᵒᵈ => J k.ofDual)] :
    IsRingFiltration (fun k : ℕᵒᵈ => tensorFiltration R I J k.ofDual)
      (fun k : ℕᵒᵈ => tensorFiltration R I J (k.ofDual + 1)) where
  mono i j h := tensorFiltration_antitone R I J h
  is_le {i j} h := by
    have hij : j.ofDual < i.ofDual := h
    exact tensorFiltration_antitone R I J (by omega)
  is_sup K k h := h (OrderDual.toDual (k.ofDual + 1)) (Nat.lt_succ_self _)
  one_mem := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_tensorFiltration R (I := I) (J := J)
      (a := 0) (b := 0) le_rfl
      (SetLike.one_mem_graded (fun k : ℕᵒᵈ => I k.ofDual))
      (SetLike.one_mem_graded (fun k : ℕᵒᵈ => J k.ofDual))
  mul_mem {i j x y} hx hy :=
    tensorFiltration_mul_le R I J
      (fun a b => mul_le.mpr fun _ hx _ hy => SetLike.mul_mem_graded
        (A := fun k : ℕᵒᵈ => I k.ofDual) (i := OrderDual.toDual a) (j := OrderDual.toDual b) hx hy)
      (fun a b => mul_le.mpr fun _ hx _ hy => SetLike.mul_mem_graded
        (A := fun k : ℕᵒᵈ => J k.ofDual) (i := OrderDual.toDual a) (j := OrderDual.toDual b) hx hy)
      i.ofDual j.ofDual (mul_mem_mul hx hy)

end Ideal

namespace Mei.AlgFiltration

variable (R : Type*) {A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] (F : Mei.AlgFiltration A) (G : Mei.AlgFiltration B)

/-- The total-degree filtration on the tensor product of two filtered algebras. -/
noncomputable def tensorProduct : Mei.AlgFiltration (A ⊗[R] B) where
  ideal := Ideal.tensorFiltration R F.ideal G.ideal
  isTwoSided _ := inferInstance
  antitone := Ideal.tensorFiltration_antitone R F.ideal G.ideal
  ideal_zero := Ideal.tensorFiltration_zero R F.ideal G.ideal F.ideal_zero G.ideal_zero
  mul_mem hx hy := Ideal.tensorFiltration_mul_le R F.ideal G.ideal
    (fun _ _ => Ideal.mul_le.mpr fun _ hx _ hy => F.mul_mem hx hy)
    (fun _ _ => Ideal.mul_le.mpr fun _ hx _ hy => G.mul_mem hx hy) _ _
    (Ideal.mul_mem_mul hx hy)

/-- The bundled tensor filtration uses the total-degree tensor ideals. -/
@[simp]
theorem tensorProduct_ideal (k : ℕ) :
    (F.tensorProduct R G).ideal k = Ideal.tensorFiltration R F.ideal G.ideal k := (rfl)

/-- The left inclusion preserves filtration orders. -/
theorem includeLeft_mem_tensorProduct {k : ℕ} {a : A} (ha : a ∈ F.ideal k) :
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := B) a ∈
      (F.tensorProduct R G).ideal k := by
  exact Ideal.tmul_mem_tensorFiltration R (a := k) (b := 0) (by omega) ha
    (by simp)

/-- The right inclusion preserves filtration orders. -/
theorem includeRight_mem_tensorProduct {k : ℕ} {b : B} (hb : b ∈ G.ideal k) :
    Algebra.TensorProduct.includeRight (R := R) (A := A) b ∈ (F.tensorProduct R G).ideal k := by
  exact Ideal.tmul_mem_tensorFiltration R (a := 0) (b := k) (by omega)
    (by simp) hb

end Mei.AlgFiltration
