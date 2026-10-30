/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Skew.Factorization.Basic
public import Mei.GroupTheory.CompletedGroup.OrderedProduct

/-!
# Assembling dilogarithm factorizations across cutoffs

Finite dilogarithm factorizations on different inventories can be compared by
adjoining identity factors in their common order. Their exponents agree at every
degree retained by the cutoff. Consequently finite factorizations of one completed
label, chosen independently at every order, determine a unique exponent family.
Its product through each cutoff recovers the original label.

The order on the index set is fixed throughout; it need not be a slope order.
The degree map is injective, but the alternating form may be zero or degenerate,
and the rational coefficient algebra may have zero divisors. The construction
does not assert existence or positivity of finite factorizations.

We use `eq_of_projection_prod_rayExp_smul_negDilogNeg_eq` for coefficient
uniqueness and `Finset.prod_map_sort_subset` for identity padding. This is the
compatibility argument for finite-order dilogarithm factorizations in Nakanishi,
*Cluster algebras and scattering diagrams, Part III*, §5.2
(arXiv:2111.00800v6), with the convention of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.SkewLieAlgebra

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

/-- A product on a fixed inventory determines precisely the visible exponents. -/
@[simp]
theorem projection_orderedDilogProduct_eq_iff (hinj : Function.Injective m)
    (s : Finset ι) (c c' : ι → R) (k : ℕ) :
    CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 s c) =
        CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 s c') ↔
      ∀ i ∈ s, d.degree (m i) ≤ k → c i = c' i := by
  let l := s.sort
  have he (a : ι → R) :
      (List.ofFn fun j : Fin l.length => factor a (l.get j)).prod =
        orderedDilogProduct β hβ m hm hm0 s a := by
    simpa only [List.ofFn_get, Function.comp_def, orderedDilogProduct_def] using congrArg List.prod
      (List.map_ofFn (f := l.get) (g := fun i => factor a i)).symm
  have h := projection_prod_rayExp_smul_negDilogNeg_eq_iff β hβ
    (fun j : Fin l.length => m (l.get j)) (fun j => hm (l.get j))
    (fun j => hm0 (l.get j)) (hinj.comp (Finset.sort_nodup s (· ≤ ·)).injective_get)
    (fun j => c (l.get j)) (fun j => c' (l.get j)) k
  rw [he c, he c'] at h
  rw [h]
  constructor
  · intro H i hi hik
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((Finset.mem_sort (· ≤ ·)).mpr hi)
    exact hj ▸ H j (hj.symm ▸ hik)
  · intro H j hj
    exact H _ ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem l j)) hj

/-- Distinct finite inventories representing the same cutoff label have the
same exponents in all visible degrees, after extending exponents by zero. -/
theorem projection_orderedDilogProduct_eq_iff_of_support
    (hinj : Function.Injective m) (s t : Finset ι) (c c' : ι → R)
    (hc : ∀ i ∉ s, c i = 0) (hc' : ∀ i ∉ t, c' i = 0) (k : ℕ) :
    CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 s c) =
        CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 t c') ↔
      ∀ i, d.degree (m i) ≤ k → c i = c' i := by
  rw [orderedDilogProduct_eq_of_subset β hβ m hm hm0 Finset.subset_union_left c
      (fun i _ hi => hc i hi),
    orderedDilogProduct_eq_of_subset β hβ m hm hm0 Finset.subset_union_right c'
      (fun i _ hi => hc' i hi),
    projection_orderedDilogProduct_eq_iff β hβ m hm hm0 hinj]
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
    exact MonoidHom.mem_ker.mp (by
      simpa only [CompletedGroup.degreeFiltration_succ] using
        rayExp_mem_degreeFiltration β hβ (hm i) (hm0 i)
          (c i • PowerSeries.negDilogNeg R) (by omega))
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
  exact (projection_orderedDilogProduct_eq_iff β hβ m hm hm0 hinj _ c a k).mp he
    i (by simpa only [Finset.mem_preimage, Set.Finite.mem_toFinset,
      PositiveDegrees.mem_cutoff] using And.intro (hm i) hi) hi

omit [LinearOrder ι] in
/-- An arbitrary exponent family on distinct positive degrees has only finitely
many nonidentity dilogarithm factors at every order. -/
theorem hasFiniteSupport_rayExp_smul_negDilogNeg (hinj : Function.Injective m)
    (c : ι → R) : CompletedGroup.HasFiniteSupport (fun i => factor c i) := by
  intro k
  apply ((d.finite_cutoff k).preimage hinj.injOn).subset
  intro i hi
  refine d.mem_cutoff.mpr ⟨hm i, ?_⟩
  by_contra hhigh
  apply hi
  exact MonoidHom.mem_ker.mp (by
    simpa only [CompletedGroup.degreeFiltration_succ] using
      rayExp_mem_degreeFiltration β hβ (hm i) (hm0 i)
        (c i • PowerSeries.negDilogNeg R) (by omega))

/-- The canonical completed ordered product of an exponent family is computed
by its finite products through the positive-degree cutoffs. -/
@[simp↓] -- Compute on the degree cutoff before expanding a generic ordered product.
theorem projection_orderedProd_rayExp_smul_negDilogNeg (hinj : Function.Injective m)
    (c : ι → R) (k : ℕ) :
    CompletedGroup.projection k (CompletedGroup.orderedProd (fun i => factor c i)
        (hasFiniteSupport_rayExp_smul_negDilogNeg β hβ m hm hm0 hinj c)) =
      CompletedGroup.projection k
        (orderedDilogProduct β hβ m hm hm0 (inventory hinj k) c) := by
  rw [CompletedGroup.projection_orderedProd_of_support _ _ k (inventory hinj k)]
  · simp only [orderedDilogProduct_def, map_list_prod, List.map_map, Function.comp_def]
  · intro i hi
    by_contra hnot
    have hk : k < d.degree (m i) := by
      simpa only [Finset.mem_preimage, Set.Finite.mem_toFinset,
        PositiveDegrees.mem_cutoff, hm i, true_and, not_le] using hnot
    apply hi
    exact MonoidHom.mem_ker.mp (by
      simpa only [CompletedGroup.degreeFiltration_succ] using
        rayExp_mem_degreeFiltration β hβ (hm i) (hm0 i)
          (c i • PowerSeries.negDilogNeg R) (by omega))

/-- Independently chosen finite factorizations of one completed label assemble
to a unique exponent family in the fixed index order. No compatibility of the
inventories or of the choices is assumed. The product of the assembled family
through every cutoff is the corresponding projection of the original label. -/
theorem existsUnique_orderedProd_rayExp_smul_negDilogNeg
    (hinj : Function.Injective m) (g : d.completedBCHGroup ℒ)
    (hfact : ∀ k : ℕ, ∃ a : ι →₀ R,
      CompletedGroup.projection k (orderedDilogProduct β hβ m hm hm0 a.support a) =
        CompletedGroup.projection k g) :
    ∃! c : ι → R, CompletedGroup.orderedProd (fun i => factor c i)
      (hasFiniteSupport_rayExp_smul_negDilogNeg β hβ m hm hm0 hinj c) = g := by
  classical
  choose a ha using hfact
  have hcoh {k l : ℕ} (hkl : k ≤ l) (i : ι) (hi : d.degree (m i) ≤ k) :
      a k i = a l i := by
    have hl := congrArg ((d.groupTower ℒ).map
      (CategoryTheory.homOfLE hkl).op) (ha l)
    simp only [CompletedGroup.map_projection] at hl
    exact (projection_orderedDilogProduct_eq_iff_of_support β hβ m hm hm0 hinj
      (a k).support (a l).support (a k) (a l)
      (fun j hj => Finsupp.notMem_support_iff.mp hj)
      (fun j hj => Finsupp.notMem_support_iff.mp hj) k).mp
        ((ha k).trans hl.symm) i hi
  let c : ι → R := fun i => a (d.degree (m i)).toNat i
  have hci (k : ℕ) (i : ι) (hi : d.degree (m i) ≤ k) : c i = a k i :=
    hcoh (by omega) i (Int.self_le_toNat _)
  have hc (k : ℕ) : CompletedGroup.projection k
      (orderedDilogProduct β hβ m hm hm0 (inventory hinj k) c) =
        CompletedGroup.projection k g := by
    calc
      _ = CompletedGroup.projection k
          (orderedDilogProduct β hβ m hm hm0 (inventory hinj k) (a k)) :=
        (projection_orderedDilogProduct_eq_iff β hβ m hm hm0 hinj _ c (a k) k).mpr
          (fun i _ hi => hci k i hi)
      _ = _ := (projection_orderedDilogProduct_cutoff
        β hβ m hm hm0 hinj (a k) k).trans (ha k)
  refine ⟨c, CompletedGroup.ext (fun k =>
    (projection_orderedProd_rayExp_smul_negDilogNeg β hβ m hm hm0 hinj c k).trans (hc k)), ?_⟩
  intro c' hc'
  funext i
  have he := congrArg (CompletedGroup.projection (d.degree (m i)).toNat) hc'
  rw [projection_orderedProd_rayExp_smul_negDilogNeg β hβ m hm hm0 hinj c'] at he
  exact eq_of_projection_orderedDilogProduct_cutoff β hβ m hm hm0 hinj c'
    (a (d.degree (m i)).toNat) (he.trans (ha _).symm) i (Int.self_le_toNat _)

end Mei.SkewLieAlgebra
