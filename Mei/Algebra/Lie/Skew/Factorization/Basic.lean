/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Skew.Dilogarithm
public import Mei.Algebra.BigOperators.Group.Finset.Ordered

/-!
# Uniqueness of dilogarithm exponents through a cutoff

On a fixed finite inventory of distinct nonzero positive degrees, in any fixed
order, a product of dilogarithm powers determines exactly the exponents in
degrees retained by a cutoff. In particular the completed product determines
all exponents. No order or nondegeneracy assumption on the alternating form,
and no domain assumption on the rational coefficient algebra, is required.

This gives a coefficient criterion for comparing finite-order factorizations:
two products representing the same label at possibly different cutoffs have
the same exponents through the smaller cutoff. Finite inventories can differ:
adjoining identity factors compares them in their common index order. Distinctness
of degrees is required only on those inventories. The ordered products and their
cutoff formulas do not assert uniqueness under arbitrary reordering.

The finite-inventory comparison uses `Finset.prod_map_sort_subset` for identity
padding. The degree induction follows `inv_prod_filter_mul_mem_and_logComponent`:
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

section FiniteTuple

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
  · rw [projection_rayExp_eq_one_of_lt β hβ (hm i) (hm0 i) _ (by omega),
      projection_rayExp_eq_one_of_lt β hβ (hm i) (hm0 i) _ (by omega)]

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

end FiniteTuple

section OrderedInventory

variable {R Γ ι : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [DecidableEq Γ] [LinearOrder ι]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  (m : ι → Γ) (hm : ∀ i, m i ∈ d.monoid) (hm0 : ∀ i, m i ≠ 0)

local notation "ℒ" => positiveGrading β hβ d
local notation "inventory" hi:arg k:arg => Finset.preimage
  (Set.Finite.toFinset (PositiveDegrees.finite_cutoff d k)) m (Function.Injective.injOn hi)
local notation "factor" c:arg i:arg => rayExp β hβ (hm i) (hm0 i) (c i • PowerSeries.negDilogNeg R)

/-- The finite dilogarithm product in increasing index order, with smallest
index leftmost. Zero exponents contribute identity factors. -/
def orderedDilogProduct (s : Finset ι) (c : ι → R) : d.completedBCHGroup ℒ :=
  (s.sort.map fun i => factor c i).prod

/-- The ordered product is computed by sorting its finite inventory. -/
theorem orderedDilogProduct_def (s : Finset ι) (c : ι → R) :
    orderedDilogProduct β hβ m hm hm0 s c = (s.sort.map fun i => factor c i).prod := (rfl)

/-- An empty inventory represents the identity label. -/
@[simp]
theorem orderedDilogProduct_empty (c : ι → R) :
    orderedDilogProduct β hβ m hm hm0 ∅ c = 1 := by
  simp [orderedDilogProduct]

/-- A singleton product is its dilogarithm factor. -/
@[simp]
theorem orderedDilogProduct_singleton (i : ι) (c : ι → R) :
    orderedDilogProduct β hβ m hm hm0 {i} c = factor c i := by
  simp [orderedDilogProduct]

/-- Zero exponents represent the identity on any finite inventory. -/
@[simp]
theorem orderedDilogProduct_zero (s : Finset ι) :
    orderedDilogProduct β hβ m hm hm0 s 0 = 1 := by
  simp [orderedDilogProduct]

/-- Adjoining degrees with zero exponent leaves the ordered product unchanged. -/
theorem orderedDilogProduct_eq_of_subset {s t : Finset ι} (hst : s ⊆ t)
    (c : ι → R) (hc : ∀ i ∈ t, i ∉ s → c i = 0) :
    orderedDilogProduct β hβ m hm hm0 s c = orderedDilogProduct β hβ m hm hm0 t c := by
  apply Finset.prod_map_sort_subset hst
  intro i hi his
  simp [hc i hi his]

/-- A product on a fixed inventory of distinct degrees determines precisely the
visible exponents. Degrees outside the inventory may coincide. -/
@[simp]
theorem projection_orderedDilogProduct_eq_iff (s : Finset ι)
    (hinj : Set.InjOn m (↑s : Set ι)) (c c' : ι → R) (k : ℕ) :
    CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 s c) =
        CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 s c') ↔
      ∀ i ∈ s, d.degree (m i) ≤ k → c i = c' i := by
  let l := s.sort
  have he (a : ι → R) :
      (List.ofFn fun j : Fin l.length => factor a (l.get j)).prod =
        orderedDilogProduct β hβ m hm hm0 s a := by
    simpa only [List.ofFn_get, Function.comp_def, orderedDilogProduct_def] using congrArg List.prod
      (List.map_ofFn (f := l.get) (g := fun i => factor a i)).symm
  have hinj' : Function.Injective (fun j : Fin l.length => m (l.get j)) := by
    intro i j hij
    apply (Finset.sort_nodup s (· ≤ ·)).injective_get
    exact hinj ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem l i))
      ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem l j)) hij
  have h := projection_prod_rayExp_smul_negDilogNeg_eq_iff β hβ
    (fun j : Fin l.length => m (l.get j)) (fun j => hm (l.get j))
    (fun j => hm0 (l.get j)) hinj'
    (fun j => c (l.get j)) (fun j => c' (l.get j)) k
  rw [he c, he c'] at h
  rw [h]
  constructor
  · intro H i hi hik
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((Finset.mem_sort (· ≤ ·)).mpr hi)
    exact hj ▸ H j (hj.symm ▸ hik)
  · intro H j hj
    exact H _ ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem l j)) hj

/-- Finite inventories with distinct degrees on their union representing the same
cutoff label have the same exponents in all visible degrees, after extending
exponents by zero. Degrees outside the union may coincide. -/
theorem projection_orderedDilogProduct_eq_iff_of_support
    (s t : Finset ι) (hinj : Set.InjOn m (↑(s ∪ t) : Set ι)) (c c' : ι → R)
    (hc : ∀ i ∉ s, c i = 0) (hc' : ∀ i ∉ t, c' i = 0) (k : ℕ) :
    CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 s c) =
        CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 t c') ↔
      ∀ i, d.degree (m i) ≤ k → c i = c' i := by
  rw [orderedDilogProduct_eq_of_subset β hβ m hm hm0 Finset.subset_union_left c
      (fun i _ hi => hc i hi),
    orderedDilogProduct_eq_of_subset β hβ m hm hm0 Finset.subset_union_right c'
      (fun i _ hi => hc' i hi),
    projection_orderedDilogProduct_eq_iff β hβ m hm hm0 (s ∪ t) hinj]
  constructor
  · intro H i hi
    by_cases his : i ∈ s ∪ t
    · exact H i his hi
    · simp only [Finset.mem_union, not_or] at his
      rw [hc i his.1, hc' i his.2]
  · exact fun H i _ hi => H i hi

/-- Projecting a finite factorization discards exactly the factors above the
cutoff. Missing degrees in the original support have exponent zero. -/
theorem projection_orderedDilogProduct_cutoff (hinj : Function.Injective m)
    (c : ι →₀ R) (k : ℕ) :
    CompletedGroup.projection k
        (orderedDilogProduct β hβ m hm hm0 (inventory hinj k) c) =
      CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 c.support c) := by
  simp only [orderedDilogProduct_def, map_list_prod, List.map_map, Function.comp_def]
  apply Finset.prod_map_sort_eq_of_ne_one
  intro i hi
  have hc : c i ≠ 0 := by
    intro hz
    exact hi (by simp [hz])
  have hk : d.degree (m i) ≤ k := by
    by_contra hhigh
    apply hi
    exact projection_rayExp_eq_one_of_lt β hβ (hm i) (hm0 i)
      (c i • PowerSeries.negDilogNeg R) (by omega)
  exact iff_of_true (by simpa only [Finset.mem_preimage, Set.Finite.mem_toFinset,
    PositiveDegrees.mem_cutoff] using And.intro (hm i) hk)
    (Finsupp.mem_support_iff.mpr hc)

/-- A coefficient family representing a label at a cutoff agrees with every
finite factorization of that label in every retained degree. This allows the
finite inventories to vary with the cutoff. -/
theorem eq_of_projection_orderedDilogProduct_cutoff
    (hinj : Function.Injective m) (c : ι → R) (a : ι →₀ R) {k : ℕ}
    (he : CompletedGroup.projection k
        (orderedDilogProduct β hβ m hm hm0 (inventory hinj k) c) =
      CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 a.support a))
    (i : ι) (hi : d.degree (m i) ≤ k) : c i = a i := by
  rw [← projection_orderedDilogProduct_cutoff β hβ m hm hm0 hinj a k] at he
  exact (projection_orderedDilogProduct_eq_iff β hβ m hm hm0 _ hinj.injOn c a k).mp he
    i (by simpa only [Finset.mem_preimage, Set.Finite.mem_toFinset,
      PositiveDegrees.mem_cutoff] using And.intro (hm i) hi) hi

end OrderedInventory

end Mei.SkewLieAlgebra
