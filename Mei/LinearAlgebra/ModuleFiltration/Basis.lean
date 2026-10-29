/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Finsupp
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Completed expansions in a basis

A filtration on the scalar ring induces a coefficientwise filtration on any free
module with a chosen basis. Its completion has unique expansions with completed
scalar coefficients and finite support modulo every filtration term.

This transports `ModuleFiltration.finsuppCompletionEquiv` through `Basis.repr`.
The finite quotients are described in the same way by
`ModuleFiltration.finsuppQuotientEquiv`.

In a free module with a chosen basis, an element is an ideal multiple of the
whole module exactly when all its basis coefficients lie in the ideal.
-/

public section

noncomputable section

namespace Module.Basis

variable {ι : Type*}

section Semiring

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
  (b : Basis ι R V) (F : Mei.ModuleFiltration R R)

/-- Ideal multiples of a free module are detected by its basis coefficients. -/
theorem mem_ideal_smul_top_iff_repr_mem (I : Ideal R) [I.IsTwoSided] (x : V) :
    x ∈ I • (⊤ : Submodule R V) ↔ ∀ i, b.repr x i ∈ I := by
  rw [← b.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [← Finsupp.linearCombination_apply, b.repr_linearCombination] using ha
  · intro hx
    exact ⟨b.repr x, hx, b.linearCombination_repr x⟩

/-- The coefficientwise filtration of a module in a chosen basis. -/
def coefficientFiltration : Mei.ModuleFiltration R V where
  submodule k := ((F.finsupp ι).submodule k).comap b.repr.toLinearMap
  antitone _ _ h := Submodule.comap_mono ((F.finsupp ι).antitone h)
  zero_eq_top := by simp

/-- An element lies in a basis filtration term precisely when each coefficient does. -/
@[simp]
theorem mem_coefficientFiltration_submodule (k : ℕ) (x : V) :
    x ∈ (b.coefficientFiltration F).submodule k ↔ ∀ i, b.repr x i ∈ F.submodule k := by
  rw [coefficientFiltration, Submodule.mem_comap, Mei.ModuleFiltration.mem_finsupp_submodule]
  simp only [LinearEquiv.coe_coe]

end Semiring

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
  (b : Basis ι R V) (F : Mei.ModuleFiltration R R)

private theorem comap_repr_finsupp_submodule (k : ℕ) :
    ((F.finsupp ι).submodule k).comap b.repr.toLinearMap =
      (b.coefficientFiltration F).submodule k := rfl

/-- Completed basis expansions are exactly the families of completed scalars
with finite support at each order. -/
def completedCoefficientsEquiv : (b.coefficientFiltration F).completion ≃ₗ[R]
    F.restrictedFamilies ι :=
  ((b.coefficientFiltration F).completionEquiv (F.finsupp ι) b.repr
    (b.comap_repr_finsupp_submodule F)).trans
    (F.finsuppCompletionEquiv ι)

/-- The completed coefficient expansion agrees with the original basis coordinates. -/
@[simp]
theorem completedCoefficientsEquiv_of (x : V) (i : ι) :
    (b.completedCoefficientsEquiv F ((b.coefficientFiltration F).of x)).val i =
      F.of (b.repr x i) := by
  rw [completedCoefficientsEquiv, LinearEquiv.trans_apply,
    Mei.ModuleFiltration.completionEquiv_of, Mei.ModuleFiltration.finsuppCompletionEquiv_apply,
    Mei.ModuleFiltration.completedCoefficient_of]

/-- The inverse expansion sends the canonical images of basis coordinates to the
canonical image of the original vector. -/
@[simp]
theorem completedCoefficientsEquiv_symm_of (x : V) :
    (b.completedCoefficientsEquiv F).symm
        ⟨F.of ∘ b.repr x, F.of_comp_mem_restrictedFamilies ι (b.repr x)⟩ =
      (b.coefficientFiltration F).of x := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext i
  simp

/-- A finite quotient of a basis filtration consists of finite coefficient vectors
over the corresponding scalar quotient. -/
def coefficientQuotientEquiv (k : ℕ) :
    (b.coefficientFiltration F).quotient k ≃ₗ[R] (ι →₀ F.quotient k) :=
  (Submodule.Quotient.equiv ((b.coefficientFiltration F).submodule (k + 1))
    ((F.finsupp ι).submodule (k + 1)) b.repr (by
      rw [← b.comap_repr_finsupp_submodule F]
      exact Submodule.map_comap_eq_of_surjective b.repr.surjective _)).trans
    (F.finsuppQuotientEquiv ι k)

/-- On representatives, the quotient coefficients are the classes of the basis
coordinates. -/
@[simp]
theorem coefficientQuotientEquiv_mk (k : ℕ) (x : V) (i : ι) :
    b.coefficientQuotientEquiv F k (Submodule.Quotient.mk x) i =
      Submodule.Quotient.mk (b.repr x i) := by
  rw [coefficientQuotientEquiv, LinearEquiv.trans_apply, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, Mei.ModuleFiltration.finsuppQuotientEquiv_mk, LinearEquiv.coe_coe]

/-- At each cutoff, the inverse expansion has the finite coefficients of the given
completed family. -/
@[simp]
theorem coefficientQuotientEquiv_projection_completedCoefficientsEquiv_symm
    (x : F.restrictedFamilies ι) (k : ℕ) (i : ι) :
    b.coefficientQuotientEquiv F k
        ((b.coefficientFiltration F).projection k ((b.completedCoefficientsEquiv F).symm x)) i =
      F.projection k (x.val i) := by
  rw [← F.finsuppQuotientEquiv_projection_finsuppCompletionEquiv_symm ι x k i,
    completedCoefficientsEquiv, LinearEquiv.symm_trans_apply,
    Mei.ModuleFiltration.projection_completionEquiv_symm]
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _
    ((F.finsupp ι).projection k ((F.finsuppCompletionEquiv ι).symm x))
  simp only [Submodule.mkQ_apply] at hy
  simp [← hy]

/-- Projecting a completed basis coefficient reads its finite quotient coordinate. -/
@[simp]
theorem projection_completedCoefficientsEquiv
    (x : (b.coefficientFiltration F).completion) (k : ℕ) (i : ι) :
    F.projection k ((b.completedCoefficientsEquiv F x).val i) =
      b.coefficientQuotientEquiv F k ((b.coefficientFiltration F).projection k x) i := by
  simpa only [LinearEquiv.symm_apply_apply] using
    (b.coefficientQuotientEquiv_projection_completedCoefficientsEquiv_symm
      F (b.completedCoefficientsEquiv F x) k i).symm

end Module.Basis
