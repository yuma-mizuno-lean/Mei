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
  exact projection_rayExp_eq_one_of_lt β hβ (hm i) (hm0 i)
    (c i • PowerSeries.negDilogNeg R) (by omega)

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
    exact projection_rayExp_eq_one_of_lt β hβ (hm i) (hm0 i)
      (c i • PowerSeries.negDilogNeg R) hk

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
    exact (projection_orderedDilogProduct_eq_iff_of_support β hβ m hm hm0
      (a k).support (a l).support hinj.injOn (a k) (a l)
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
        (projection_orderedDilogProduct_eq_iff β hβ m hm hm0 _ hinj.injOn c (a k) k).mpr
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
