/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.FilteredAlgebra.Basic

/-!
# Total-degree tensor filtrations

For families `F` and `G` of submodules, `tensorFiltration F G n` is the sum of
the images of `F a ⊗ G b` for `n ≤ a + b`. For decreasing families this is already
the finite sum over `a + b = n`. No flatness or injectivity of the tensor maps
is required: we use their images, expressed by Mathlib's `Submodule.map₂` and
`TensorProduct.range_mapIncl`.

This construction supplies the module underlying the total-degree filtration on
tensor products of filtered algebras and hence their completed tensor products.
-/

public section

namespace Mei

open scoped TensorProduct

variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The sum of tensor images whose total filtration degree is at least `n`. -/
def tensorFiltration (F : ℕ → Submodule R M) (G : ℕ → Submodule R N)
    (n : ℕ) : Submodule R (M ⊗[R] N) :=
  ⨆ a, ⨆ b, ⨆ (_ : n ≤ a + b), Submodule.map₂ (TensorProduct.mk R M N) (F a) (G b)

variable (F : ℕ → Submodule R M) (G : ℕ → Submodule R N)

/-- The defining sum of tensor images. -/
theorem tensorFiltration_def (n : ℕ) :
    tensorFiltration F G n =
      ⨆ a, ⨆ b, ⨆ (_ : n ≤ a + b),
        Submodule.map₂ (TensorProduct.mk R M N) (F a) (G b) := (rfl)

/-- Each tensor image of sufficiently high total degree lies in the filtration. -/
theorem map₂_le_tensorFiltration {a b n : ℕ} (h : n ≤ a + b) :
    Submodule.map₂ (TensorProduct.mk R M N) (F a) (G b) ≤ tensorFiltration F G n := by
  rw [tensorFiltration_def]
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le h le_rfl))

/-- Pure tensors have at least the sum of the filtration degrees of their factors. -/
theorem tmul_mem_tensorFiltration {a b n : ℕ} {x : M} {y : N}
    (hx : x ∈ F a) (hy : y ∈ G b) (h : n ≤ a + b) :
    x ⊗ₜ[R] y ∈ tensorFiltration F G n :=
  map₂_le_tensorFiltration F G h (Submodule.apply_mem_map₂ _ hx hy)

/-- To bound the tensor filtration, it suffices to bound its generating pure tensors. -/
theorem tensorFiltration_le_iff {n : ℕ} {P : Submodule R (M ⊗[R] N)} :
    tensorFiltration F G n ≤ P ↔
      ∀ a b, n ≤ a + b → ∀ x ∈ F a, ∀ y ∈ G b, x ⊗ₜ[R] y ∈ P := by
  simp only [tensorFiltration_def, iSup_le_iff, Submodule.map₂_le]
  rfl

/-- Total-degree tensor filtrations decrease, even for arbitrary input families. -/
theorem tensorFiltration_antitone : Antitone (tensorFiltration F G) := by
  intro n m h
  exact (tensorFiltration_le_iff F G).mpr fun a b hab x hx y hy =>
    tmul_mem_tensorFiltration F G hx hy (h.trans hab)

/-- For decreasing input families, only pairs of total degree exactly `n` are needed. -/
theorem tensorFiltration_eq_iSup_add_eq (hF : Antitone F) (hG : Antitone G) (n : ℕ) :
    tensorFiltration F G n =
      ⨆ a, ⨆ b, ⨆ (_ : a + b = n),
        Submodule.map₂ (TensorProduct.mk R M N) (F a) (G b) := by
  apply le_antisymm
  · refine (tensorFiltration_le_iff F G).mpr fun a b hab x hx y hy => ?_
    have ha : min a n ≤ a := min_le_left _ _
    have hb : n - min a n ≤ b := by omega
    have hab' : min a n + (n - min a n) = n := by omega
    apply Submodule.mem_iSup_of_mem (min a n)
    apply Submodule.mem_iSup_of_mem (n - min a n)
    rw [iSup_pos hab']
    exact Submodule.apply_mem_map₂ _ (hF ha hx) (hG hb hy)
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    exact map₂_le_tensorFiltration F G (by omega)

/-- If both degree-zero terms are full, the tensor filtration starts with the full module. -/
@[simp]
theorem tensorFiltration_zero (hF : F 0 = ⊤) (hG : G 0 = ⊤) :
    tensorFiltration F G 0 = ⊤ := by
  apply top_unique
  simpa [hF, hG, TensorProduct.map₂_mk_top_top_eq_top] using
    map₂_le_tensorFiltration F G (a := 0) (b := 0) (n := 0) le_rfl

/-- The total-degree terms carry the standard filtration on order-dual natural indices. -/
instance tensorFiltration_isFiltration :
    IsFiltration (fun n : ℕᵒᵈ => tensorFiltration F G n.ofDual)
      (fun n : ℕᵒᵈ => tensorFiltration F G (n.ofDual + 1)) where
  mono _ _ h := tensorFiltration_antitone F G h
  is_le h := tensorFiltration_antitone F G (Nat.succ_le_of_lt h)
  is_sup P n h := h (OrderDual.toDual (n.ofDual + 1)) (by exact Nat.lt_succ_self _)

end Mei
