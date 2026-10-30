/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Skew.Dilogarithm

/-!
# Uniqueness of dilogarithm exponents through a cutoff

On a fixed finite inventory of distinct nonzero positive degrees, in any fixed
order, a product of dilogarithm powers determines exactly the exponents in
degrees retained by a cutoff. In particular the completed product determines
all exponents. No order or nondegeneracy assumption on the alternating form,
and no domain assumption on the rational coefficient algebra, is required.

This gives a coefficient criterion for comparing finite-order factorizations:
two products representing the same label at possibly different cutoffs have
the same exponents through the smaller cutoff. The inventory and its order
must be the same; this does not assert uniqueness under arbitrary reordering.

The degree induction follows `inv_prod_filter_mul_mem_and_logComponent`:
remove the already determined lower-degree factors and read the next exponent
from the leading logarithmic coefficient. This is the triangular comparison
used in Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2
(arXiv:2111.00800v6), with the dilogarithm convention of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries

variable {R Γ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  {r : ℕ} (m : Fin r → Γ) (hm : ∀ i, m i ∈ d.monoid) (hm0 : ∀ i, m i ≠ 0)

local notation "ℒ" => positiveGrading β hβ d
local notation "prodDilog" c:arg => List.prod (List.ofFn fun i =>
  rayExp β hβ (hm i) (hm0 i) (c i • negDilogNeg R))

/-- Agreement of exponents in the retained degrees suffices for agreement of
the finite products at that cutoff. Factors born later project to the identity. -/
theorem projection_prod_rayExp_smul_negDilogNeg_eq_of_eq
    (c c' : Fin r → R) (k : ℕ) (hc : ∀ i, d.degree (m i) ≤ k → c i = c' i) :
    CompletedGroup.projection k (prodDilog c) = CompletedGroup.projection k (prodDilog c') := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  by_cases hi : d.degree (m i) ≤ k
  · rw [hc i hi]
  · have hone (a : R) : CompletedGroup.projection k
        (rayExp β hβ (hm i) (hm0 i) (a • negDilogNeg R)) = 1 := by
      exact MonoidHom.mem_ker.mp (by
        simpa only [CompletedGroup.degreeFiltration_succ] using
          rayExp_mem_degreeFiltration β hβ (hm i) (hm0 i)
            (a • negDilogNeg R) (by omega))
    rw [hone, hone]

/-- A finite product at distinct degrees determines every dilogarithm exponent
whose degree is retained. The factors may be in any fixed order. -/
theorem eq_of_projection_prod_rayExp_smul_negDilogNeg_eq
    (hinj : Function.Injective m) (c c' : Fin r → R) {k : ℕ}
    (hprod : CompletedGroup.projection k (prodDilog c) = CompletedGroup.projection k (prodDilog c'))
    (i : Fin r) (hi : d.degree (m i) ≤ k) : c i = c' i := by
  classical
  simp only [List.ofFn_eq_map] at hprod
  suffices H : ∀ a : ℕ, ∀ i, (d.degree (m i)).toNat = a →
      d.degree (m i) ≤ k → c i = c' i from H _ i rfl hi
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro i hia hik
    have hpos := d.degree_pos (hm i) (hm0 i)
    have hdegree : d.degree (m i) = ((a - 1) + 1 : ℕ) := by omega
    have hlow : (((List.finRange r).filter fun j =>
        d.degree (m j) < d.degree (m i)).map fun j =>
        rayExp β hβ (hm j) (hm0 j) (c j • negDilogNeg R)).prod =
      (((List.finRange r).filter fun j =>
        d.degree (m j) < d.degree (m i)).map fun j =>
        rayExp β hβ (hm j) (hm0 j) (c' j • negDilogNeg R)).prod := by
      congr 1
      apply List.map_congr_left
      intro j hj
      have hjdeg : d.degree (m j) < d.degree (m i) := by simpa using (List.mem_filter.mp hj).2
      have hjpos := d.degree_pos (hm j) (hm0 j)
      rw [ih _ (by omega) j rfl (by omega)]
    have hc := (inv_prod_filter_mul_mem_and_logComponent β hβ m hm hm0 hinj c (k := k)
      (g := ((List.finRange r).map fun j =>
        rayExp β hβ (hm j) (hm0 j) (c j • negDilogNeg R)).prod)
      rfl i (a := a - 1) hdegree (by omega)).2
    have hc' := (inv_prod_filter_mul_mem_and_logComponent β hβ m hm hm0 hinj c' (k := k)
      hprod i (a := a - 1) hdegree (by omega)).2
    rw [← hlow] at hc'
    have he := congrArg (fun x => toFinsupp β hβ x (m i)) (hc.symm.trans hc')
    simpa only [toFinsupp_single, Finsupp.single_eq_same] using he

/-- Equality of truncated products is exactly equality of the exponents in
the degrees visible at that order. Exponents above the cutoff remain arbitrary. -/
@[simp]
theorem projection_prod_rayExp_smul_negDilogNeg_eq_iff
    (hinj : Function.Injective m) (c c' : Fin r → R) (k : ℕ) :
    CompletedGroup.projection k (prodDilog c) = CompletedGroup.projection k (prodDilog c') ↔
      ∀ i, d.degree (m i) ≤ k → c i = c' i :=
  ⟨fun h i hi => eq_of_projection_prod_rayExp_smul_negDilogNeg_eq
      β hβ m hm hm0 hinj c c' h i hi,
    projection_prod_rayExp_smul_negDilogNeg_eq_of_eq β hβ m hm hm0 c c' k⟩

/-- The completed product at a fixed ordered inventory of distinct degrees
determines all its exponents, including degrees in the radical of the form. -/
@[simp]
theorem prod_rayExp_smul_negDilogNeg_eq_iff
    (hinj : Function.Injective m) (c c' : Fin r → R) :
    prodDilog c = prodDilog c' ↔ c = c' := by
  constructor
  · intro h
    funext i
    exact eq_of_projection_prod_rayExp_smul_negDilogNeg_eq β hβ m hm hm0 hinj c c'
      (congrArg (CompletedGroup.projection (d.degree (m i)).toNat) h) i
      (Int.self_le_toNat _)
  · rintro rfl
    rfl

/-- Finite factorizations of the same completed label at two cutoffs have
identical exponents through the smaller cutoff, on the same ordered inventory. -/
theorem eq_of_projection_prod_rayExp_smul_negDilogNeg_eq_of_le
    (hinj : Function.Injective m) (c c' : Fin r → R) {g : d.completedBCHGroup ℒ}
    {k l : ℕ} (hkl : k ≤ l)
    (hc : CompletedGroup.projection k (prodDilog c) = CompletedGroup.projection k g)
    (hc' : CompletedGroup.projection l (prodDilog c') = CompletedGroup.projection l g)
    (i : Fin r) (hi : d.degree (m i) ≤ k) : c i = c' i := by
  apply eq_of_projection_prod_rayExp_smul_negDilogNeg_eq β hβ m hm hm0 hinj c c' _ i hi
  have he := congrArg ((d.groupTower ℒ).map
    (CategoryTheory.homOfLE hkl).op) hc'
  simp only [CompletedGroup.map_projection] at he
  exact hc.trans he.symm

end Mei.SkewLieAlgebra
