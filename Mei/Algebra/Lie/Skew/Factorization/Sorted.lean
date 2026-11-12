/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Skew.Factorization.Basic
public import Mei.Algebra.Lie.Skew.Factorization.Completion
public import Mei.Algebra.Lie.Skew.Grouping
public import Mei.Data.List.InsertionSort
public import Mei.Data.List.Replicate

/-!
# Sorted products of dilogarithm factors as ordered products

A finite list of dilogarithm factors `Ψ[mᵢ]^{eᵢ}`, in which `β(mᵢ, mⱼ) ≥ 0` whenever `i`
precedes `j`, is a product over its distinct degrees in a fixed index order. Repeated degrees
are grouped (`SkewLieAlgebra.exists_nodup_prod_rayExp_eq`), and the grouped factors are put
in index order by an insertion sort. The sort only swaps factors with vanishing pairing, which
commute (`SkewLieAlgebra.commute_rayExp_of_eq_zero`), provided the index order places a pair
with positive pairing in that order. The result is the finite product `orderedDilogProduct`
with the multiplicity of each index times its exponent.

Consequently, if a completed label agrees at every order with a sorted product of factors
`Ψ[mᵢ]^{eᵢ}`, the lists chosen separately at each order, then it is the completed ordered
product `∏ᵢ Ψ[mᵢ]^{sᵢ eᵢ}` over all indices, for unique natural numbers `sᵢ` when the `eᵢ` are
nonzero (`SkewLieAlgebra.existsUnique_orderedProd_rayExp_nsmul_smul_negDilogNeg`).
-/

public noncomputable section

open TauCeti (PositiveDegrees)

namespace Mei.SkewLieAlgebra

open PowerSeries

variable {R Γ ι : Type*} [CommRing R] [Algebra ℚ R] [PartialOrder R] [IsOrderedAddMonoid R]
  [AddCommGroup Γ] [DecidableEq Γ] [LinearOrder ι]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  (m : ι → Γ) (hm : ∀ i, m i ∈ d.monoid) (hm0 : ∀ i, m i ≠ 0)

/-- **A sorted product is an ordered product.** Let the index order be compatible with the
pairing, `i ≤ j` whenever `β(mᵢ, mⱼ) > 0`, on distinct degrees. A product of dilogarithm
factors `Ψ[mᵢ]^{eᵢ}` over a list `l` with `β(mᵢ, mⱼ) ≥ 0` for `i` before `j` equals the
ordered product of the factors `Ψ[mᵢ]^{(count i l) eᵢ}`, over the distinct indices of `l`. -/
theorem exists_prod_rayExp_eq_orderedDilogProduct (hinj : Function.Injective m)
    (hord : ∀ i j, 0 < β (m i) (m j) → i ≤ j) (e : ι → R) (l : List ι)
    (hl : l.Pairwise fun i j => 0 ≤ β (m i) (m j)) :
    ∃ a : ι →₀ R, (∀ i, a i = l.count i • e i) ∧
      (l.map fun i => rayExp β hβ (hm i) (hm0 i) (e i • negDilogNeg R)).prod =
        orderedDilogProduct β hβ m hm hm0 a.support a := by
  let a : ι →₀ R := Finsupp.onFinset l.toFinset (fun i => l.count i • e i) fun i hi => by
    by_contra hil
    exact hi (by rw [List.count_eq_zero_of_not_mem (by simpa using hil), zero_smul])
  have ha (i : ι) : a i = l.count i • e i := Finsupp.onFinset_apply ..
  refine ⟨a, ha, ?_⟩
  obtain ⟨L, hLl, hcov, hnd, hLpw, hprod⟩ := exists_nodup_prod_rayExp_eq β hβ m hm hm0
    (fun i => e i • negDilogNeg R) l hl
  -- The grouped series of an index is its multiplicity times its exponent.
  have hsum (i : ι) :
      ((l.filter fun j => m j = m i).map fun j => e j • negDilogNeg R).sum =
        a i • negDilogNeg R := by
    rw [List.filter_eq_replicate_count_of_injective hinj, List.map_replicate,
      List.sum_replicate, ha, smul_assoc]
  simp only [hsum] at hprod
  have hLnd : L.Nodup := List.Nodup.of_map m hnd
  have hLmem (i : ι) : i ∈ L ↔ i ∈ l := by
    refine ⟨fun h => hLl h, fun h => ?_⟩
    obtain ⟨j, hj, hji⟩ := hcov i h
    exact hinj hji ▸ hj
  -- Sorting the grouped factors only swaps factors with vanishing pairing.
  have hcomm : L.Pairwise fun i j => i ≤ j ∨ Commute
      (rayExp β hβ (hm i) (hm0 i) (a i • negDilogNeg R))
      (rayExp β hβ (hm j) (hm0 j) (a j • negDilogNeg R)) :=
    hLpw.imp fun {i j} h => (eq_or_lt_of_le h).elim
      (fun h0 => Or.inr (commute_rayExp_of_eq_zero β hβ _ _ _ _ h0.symm _ _))
      fun hpos => Or.inl (hord i j hpos)
  set M := L.insertionSort (· ≤ ·) with hM
  have hMmem (i : ι) : i ∈ M ↔ i ∈ l := (List.mem_insertionSort _).trans (hLmem i)
  have hMnd : M.Nodup := ((List.perm_insertionSort _ L).nodup_iff).mpr hLnd
  have hMsort : M.toFinset.sort = M :=
    (List.toFinset_sort (r := (· ≤ ·)) hMnd).mpr (List.pairwise_insertionSort _ L)
  have hMfin : M.toFinset = l.toFinset := by
    ext i
    simp only [List.mem_toFinset, hMmem]
  have hsupp : a.support ⊆ l.toFinset := Finsupp.support_onFinset_subset
  rw [hprod, ← List.prod_map_insertionSort (· ≤ ·) _ hcomm,
    orderedDilogProduct_eq_of_subset β hβ m hm hm0 hsupp a fun i _ hi =>
      Finsupp.notMem_support_iff.mp hi,
    orderedDilogProduct_def, ← hMfin, hMsort]

/-- **Sorted factorizations at every order assemble.** Let the index order be compatible with the
pairing, `i ≤ j` whenever `β(mᵢ, mⱼ) > 0`, on distinct degrees, and fix nonzero exponents
`e : ι → R`. Suppose that at every order `k` the label `g` agrees with a product of factors
`Ψ[mᵢ]^{eᵢ}` over a list of indices in which `β(mᵢ, mⱼ) ≥ 0` whenever `i` precedes `j`, the list
being chosen separately at each order. Then `g` is the completed ordered product
`∏ᵢ Ψ[mᵢ]^{sᵢ eᵢ}` over all indices for exactly one family of natural numbers `sᵢ`; `sᵢ` is the
multiplicity of `i` in the list chosen at the order `deg mᵢ`. -/
theorem existsUnique_orderedProd_rayExp_nsmul_smul_negDilogNeg (hinj : Function.Injective m)
    (hord : ∀ i j, 0 < β (m i) (m j) → i ≤ j) (e : ι → R)
    (he : ∀ i, e i ≠ 0) (g : d.completedBCHGroup (positiveGrading β hβ d))
    (hfact : ∀ k : ℕ, ∃ l : List ι, l.Pairwise (fun i j => 0 ≤ β (m i) (m j)) ∧
      TauCeti.CompletedGroup.projection k
          (l.map fun i => rayExp β hβ (hm i) (hm0 i) (e i • negDilogNeg R)).prod =
        TauCeti.CompletedGroup.projection k g) :
    ∃! s : ι → ℕ, TauCeti.CompletedGroup.orderedProd
        (fun i => rayExp β hβ (hm i) (hm0 i) ((s i • e i) • negDilogNeg R))
        (hasFiniteSupport_rayExp_smul_negDilogNeg β hβ m hm hm0 hinj fun i => s i • e i) = g := by
  choose l hl hlg using hfact
  choose a ha hprod using fun k =>
    exists_prod_rayExp_eq_orderedDilogProduct β hβ m hm hm0 hinj hord e (l k) (hl k)
  obtain ⟨c, hc, huniq⟩ := existsUnique_orderedProd_rayExp_smul_negDilogNeg β hβ m hm hm0 hinj g
    fun k => ⟨a k, by rw [← hprod, hlg]⟩
  -- The assembled exponent at `i` is read off from the list chosen at the order `deg mᵢ`.
  have hcs (i : ι) : c i = (l (d.degree (m i)).toNat).count i • e i := by
    rw [← ha]
    exact eq_of_orderedProd_rayExp_smul_negDilogNeg_eq β hβ m hm hm0 hinj c (a _) hc
      (by rw [← hprod, hlg]) i (Int.self_le_toNat _)
  obtain rfl : c = fun i => (l (d.degree (m i)).toNat).count i • e i := funext hcs
  refine ⟨_, hc, fun s hs => funext fun i => ?_⟩
  have h := congrFun (huniq (fun i => s i • e i) hs) i
  simp only [← Nat.cast_smul_eq_nsmul ℚ] at h
  exact_mod_cast smul_left_injective ℚ (he i) h

end Mei.SkewLieAlgebra
