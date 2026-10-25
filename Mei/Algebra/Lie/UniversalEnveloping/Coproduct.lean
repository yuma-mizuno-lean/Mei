/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Basic

/-!
# The coproduct preserves total degree

For a graded Lie algebra with nonnegative support relative to an integer-valued
degree map, the enveloping coproduct preserves the decreasing degree filtration
when the target carries the total-degree filtration `Ideal.tensorFiltration`.
On Lie generators, the coproduct is given by the primitive-generator formula
`TauCeti.UniversalEnvelopingAlgebra.comul_ι`.

Preservation induces algebra maps from finite-degree enveloping quotients to
tensor-product quotients by total degree, compatible with lowering the cutoff.
These maps supply the finite-order coproducts for passage to degree completions.
The results hold over every commutative ring without a basis or
bounded-generation assumption.
-/

public section

open scoped TensorProduct

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d hneg
local notation "T" => Ideal.tensorFiltration R
  (Mei.AlgFiltration.ideal (degreeFiltration ℒ d hneg))
  (Mei.AlgFiltration.ideal (degreeFiltration ℒ d hneg))
local notation "Δ" => Bialgebra.comulAlgHom R U

private theorem comul_generator_mem_tensorFiltration {n : Γ} (x : ℒ n) :
    Δ (ι R (x : L)) ∈ T (d n).toNat := by
  by_cases hn : d n < 0
  · have hx : (x : L) = 0 := by
      simpa only [hneg n hn, Submodule.mem_bot] using x.property
    simp only [hx, map_zero, Ideal.zero_mem]
  · have hnd : (((d n).toNat : ℕ) : ℤ) ≤ d n := by omega
    have hx := ι_mem_degreeFiltration ℒ d hneg x.property hnd
    have h1 : (1 : U) ∈ (F).ideal 0 := by rw [(F).ideal_zero]; trivial
    rw [Bialgebra.comulAlgHom_apply, TauCeti.UniversalEnvelopingAlgebra.comul_ι]
    apply Ideal.add_mem
    · exact Ideal.tmul_mem_tensorFiltration R (by omega) hx h1
    · exact Ideal.tmul_mem_tensorFiltration R (by omega) h1 hx

private theorem comul_word_mem_tensorFiltration (l : List (Σ i, ℒ i)) :
    Δ (l.map (fun x => ι R (x.2 : L))).prod ∈ T (d (l.map Sigma.fst).sum).toNat := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero, Int.toNat_zero, map_one]
    rw [Ideal.tensorFiltration_zero R (F).ideal (F).ideal (F).ideal_zero (F).ideal_zero]
    trivial
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, map_add]
    have hmul := Ideal.tensorFiltration_mul_le R (F).ideal (F).ideal
      (fun _ _ => Ideal.mul_le.mpr fun _ hx _ hy => (F).mul_mem hx hy)
      (fun _ _ => Ideal.mul_le.mpr fun _ hx _ hy => (F).mul_mem hx hy)
      (d a.1).toNat (d (l.map Sigma.fst).sum).toNat
      (Ideal.mul_mem_mul (comul_generator_mem_tensorFiltration ℒ d hneg a.2) ih)
    exact Ideal.tensorFiltration_antitone R (F).ideal (F).ideal (by omega) hmul

/-- The enveloping coproduct sends each degree ideal into the corresponding
total-degree tensor ideal. -/
theorem degreeFiltration_le_comap_comul (k : ℕ) :
    (F).ideal k ≤ (T k).comap (Δ).toRingHom := by
  rw [Mei.UniversalEnvelopingAlgebra.degreeFiltration_ideal,
    GradedAlgebra.degreeIdeal_le_iff]
  intro n hn
  apply (homogeneousSubmodule_le_iff ℒ n (((T k).comap (Δ).toRingHom).restrictScalars R)).mpr
  intro l hl
  have hw := comul_word_mem_tensorFiltration ℒ d hneg l
  exact Ideal.tensorFiltration_antitone R (F).ideal (F).ideal (by rw [hl]; omega) hw

/-- The coproduct induced on a finite degree quotient, with its tensor target
quotiented by total degree. -/
noncomputable def quotientCoproduct (k : ℕ) :
    U ⧸ (F).ideal k →ₐ[R] (U ⊗[R] U) ⧸ T k :=
  Ideal.quotientMapₐ (T k) Δ (degreeFiltration_le_comap_comul ℒ d hneg k)

/-- The quotient coproduct applies the ordinary coproduct to representatives. -/
@[simp]
theorem quotientCoproduct_mk (k : ℕ) (x : U) :
    quotientCoproduct ℒ d hneg k (Ideal.Quotient.mk ((F).ideal k) x) =
      Ideal.Quotient.mk (T k) (Coalgebra.comul (R := R) x) := by
  rw [quotientCoproduct]
  simpa only [Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply] using
    (Ideal.quotient_map_mkₐ (T k) Δ (degreeFiltration_le_comap_comul ℒ d hneg k) (x := x))

/-- Quotient coproducts commute with lowering the degree cutoff. -/
theorem factor_quotientCoproduct {k l : ℕ} (h : k ≤ l) (x : U ⧸ (F).ideal l) :
    Ideal.Quotient.factor (Ideal.tensorFiltration_antitone R (F).ideal (F).ideal h)
        (quotientCoproduct ℒ d hneg l x) =
      quotientCoproduct ℒ d hneg k (Ideal.Quotient.factor ((F).antitone h) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientCoproduct_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factor_mk, quotientCoproduct_mk]

end Mei.UniversalEnvelopingAlgebra
