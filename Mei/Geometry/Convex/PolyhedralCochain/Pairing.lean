/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Basic
public import Mei.Geometry.Affine.Transverse
public import Mei.Analysis.Convex.Intrinsic

/-!
# Intersection pairing with affine test simplices

An affine test simplex of dimension `k` is given by its vertices `v : Fin (k + 1) → V`. It is
the image `convexHull ℝ (range v)` of the standard simplex under the affine map sending the
standard vertices to `v`, and its linear part sends the positively oriented standard frame to the
edge frame `(v 1 - v 0, …, v k - v 0)`. The test is transverse to an oriented cell `σ` of
codimension `k` when its image avoids the relative boundary of `σ` and, if it meets `σ`, its edge
frame maps to a basis of the normal quotient `V ⧸ dir σ`. If the test meets `σ`, it meets the
affine span of `σ` in a single point, a relative interior point of `σ`. Disjoint tests may be
degenerate.

The local intersection index is the sign of the conormal orientation of `σ` on the edge frame
when the test meets `σ`, and zero otherwise. For a transverse test it vanishes exactly when the
test misses `σ`, and it changes sign with the orientation. Extending linearly gives the
intersection pairing of a test with finite formal sums of oriented cells, with values in the
coefficient module, natural in the coefficients.

The cochain relations preserve the pairing whenever the test is transverse to both
representatives (`PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq`), although the cells
of the connecting relation need not be transverse to the test. The proof groups cells by affine
span; the test meets each relevant span in a single point. Near that point, within the span, the
local coefficient of a transverse formal sum is constant, while every relation has vanishing
local coefficient off a nowhere dense subset of the span (`IsNowhereDense`).
-/

public section

open Set Topology

noncomputable section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

namespace OrientedCell

/-- The affine test simplex with vertices `v` is transverse to the oriented cell `σ` of the same
codimension: its image avoids the relative boundary of `σ` and, if it meets `σ`, its edge frame
`(v 1 - v 0, …, v k - v 0)` is linearly independent modulo the direction of `σ`, so that the
linear part of the test is an isomorphism onto the normal quotient. -/
structure IsTransverse (σ : OrientedCell h k) (v : Fin (k + 1) → V) : Prop where
  /-- The test avoids the relative boundary of the cell. -/
  disjoint_intrinsicFrontier :
    Disjoint (convexHull ℝ (range v)) (intrinsicFrontier ℝ σ.carrier)
  /-- Where the test meets the cell, its edge frame is a basis of the normal quotient. -/
  linearIndependent : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty →
    LinearIndependent ℝ
      ((affineSpan ℝ σ.carrier).direction.mkQ ∘ fun j : Fin k => v j.succ - v 0)

variable {σ : OrientedCell h k} {v : Fin (k + 1) → V}

/-- Reversing a cell's orientation preserves transversality of an affine test simplex. -/
@[simp]
theorem isTransverse_reverse_iff (σ : OrientedCell h k) (v : Fin (k + 1) → V) :
    σ.reverse.IsTransverse v ↔ σ.IsTransverse v := by
  constructor <;> intro hv <;>
    refine ⟨by simpa only [reverse_carrier] using hv.disjoint_intrinsicFrontier, ?_⟩
  · have hlin := hv.linearIndependent
    rw [reverse_carrier] at hlin
    exact hlin
  · rw [reverse_carrier]
    exact hv.linearIndependent

/-- A transverse test meeting a cell meets its affine span in only one point. -/
theorem IsTransverse.subsingleton_convexHull_inter_affineSpan (hv : σ.IsTransverse v)
    (hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty) :
    (convexHull ℝ (range v) ∩ affineSpan ℝ σ.carrier).Subsingleton :=
  ((affineSpan ℝ σ.carrier).subsingleton_affineSpan_range_inter
    (hv.linearIndependent hmeet)).anti
    (inter_subset_inter_left _ (convexHull_subset_affineSpan _))

/-- A transverse test meets a cell only at relative interior points. -/
theorem IsTransverse.mem_intrinsicInterior (hv : σ.IsTransverse v) {x : V}
    (hxv : x ∈ convexHull ℝ (range v)) (hxσ : x ∈ σ.carrier) :
    x ∈ intrinsicInterior ℝ σ.carrier := by
  rw [← intrinsicClosure_sdiff_intrinsicFrontier]
  exact ⟨subset_intrinsicClosure hxσ, hv.disjoint_intrinsicFrontier.notMem_of_mem_left hxv⟩

open Classical in
/-- The local intersection index of the affine test simplex with vertices `v` at the cell `σ`:
the sign of the conormal orientation of `σ` on the edge frame `(v 1 - v 0, …, v k - v 0)` if the
test meets `σ`, and zero otherwise. -/
def intersectionIndex (σ : OrientedCell h k) (v : Fin (k + 1) → V) : ℤ :=
  if (convexHull ℝ (range v) ∩ σ.carrier).Nonempty then
    σ.orientation.evalSign (fun j : Fin k => v j.succ - v 0)
  else 0

/-- A test meeting a cell has the orientation sign on its edge frame as intersection index. -/
theorem intersectionIndex_of_nonempty
    (hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty) :
    σ.intersectionIndex v = σ.orientation.evalSign (fun j : Fin k => v j.succ - v 0) := by
  rw [intersectionIndex, ite_eq_left hmeet]

/-- A test disjoint from a cell has intersection index zero. -/
theorem intersectionIndex_of_disjoint (hdisj : Disjoint (convexHull ℝ (range v)) σ.carrier) :
    σ.intersectionIndex v = 0 := by
  rw [intersectionIndex, ite_eq_right (not_nonempty_iff_eq_empty.mpr hdisj.inter_eq)]

/-- Reversing the orientation of a cell negates its intersection index. -/
@[simp]
theorem intersectionIndex_reverse (σ : OrientedCell h k) (v : Fin (k + 1) → V) :
    σ.reverse.intersectionIndex v = -σ.intersectionIndex v := by
  by_cases hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty
  · rw [intersectionIndex_of_nonempty hmeet,
      intersectionIndex_of_nonempty (σ := σ.reverse) (by rwa [reverse_carrier]),
      reverse_orientation, Module.Ray.evalSign_neg, SignType.coe_neg]
  · have hdisj : Disjoint (convexHull ℝ (range v)) σ.carrier :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet)
    rw [intersectionIndex_of_disjoint hdisj,
      intersectionIndex_of_disjoint (σ := σ.reverse) (by rwa [reverse_carrier]), neg_zero]

/-- The intersection index of a transverse test vanishes exactly when the test misses the cell;
otherwise it is `±1`. -/
theorem IsTransverse.intersectionIndex_eq_zero_iff (hv : σ.IsTransverse v) :
    σ.intersectionIndex v = 0 ↔ Disjoint (convexHull ℝ (range v)) σ.carrier := by
  have := h.finiteDimensional
  refine ⟨fun hzero => ?_, intersectionIndex_of_disjoint⟩
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hmeet
  have hne := (σ.isConormal.evalSign_ne_zero_iff
    (σ.finrank_quotient_direction.trans (Fintype.card_fin k).symm) _).mpr
    (hv.linearIndependent hmeet)
  rw [intersectionIndex_of_nonempty hmeet] at hzero
  generalize σ.orientation.evalSign _ = s at hzero hne
  cases s <;> simp_all

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

/-- The intersection pairing of the affine test simplex with vertices `v` with finite formal sums
of oriented cells: the sum of the coefficients weighted by the local intersection indices. -/
def intersectionPairing (v : Fin (k + 1) → V) : (OrientedCell h k →₀ E) →ₗ[R] E :=
  Finsupp.lsum ℕ fun σ => σ.intersectionIndex v • LinearMap.id

@[simp]
theorem intersectionPairing_single (v : Fin (k + 1) → V) (σ : OrientedCell h k) (c : E) :
    intersectionPairing (R := R) v (Finsupp.single σ c) = σ.intersectionIndex v • c := by
  simp [intersectionPairing]

theorem intersectionPairing_apply (v : Fin (k + 1) → V) (x : OrientedCell h k →₀ E) :
    intersectionPairing (R := R) v x = x.sum fun σ c => σ.intersectionIndex v • c := by
  rw [intersectionPairing, Finsupp.lsum_apply]
  exact Finsupp.sum_congr fun σ _ => by rw [LinearMap.smul_apply, LinearMap.id_apply]

/-- The intersection pairing commutes with linear maps of coefficients. -/
theorem intersectionPairing_comp_mapRange {E' : Type*} [AddCommGroup E'] [Module R E']
    (f : E →ₗ[R] E') (v : Fin (k + 1) → V) :
    intersectionPairing v ∘ₗ Finsupp.mapRange.linearMap f =
      f ∘ₗ intersectionPairing (R := R) (h := h) v := by
  ext σ c
  simp

section relations

/-! ### Local coefficients and the cochain relations -/

open Classical in
/-- The coefficient of a formal sum at the point `q` along the affine subspace `A`, measured
against the frame `f`. -/
private def localCoeff (A : AffineSubspace ℝ V) (f : Fin k → V) (q : V) :
    (OrientedCell h k →₀ E) →ₗ[R] E :=
  Finsupp.lsum ℕ fun σ => if affineSpan ℝ σ.carrier = A ∧ q ∈ σ.carrier then
    (σ.orientation.evalSign f : ℤ) • LinearMap.id else 0

open Classical in
private theorem localCoeff_single (A : AffineSubspace ℝ V) (f : Fin k → V) (q : V)
    (σ : OrientedCell h k) (c : E) :
    localCoeff (R := R) A f q (Finsupp.single σ c) =
      if affineSpan ℝ σ.carrier = A ∧ q ∈ σ.carrier then (σ.orientation.evalSign f : ℤ) • c
      else 0 := by
  rw [localCoeff, Finsupp.lsum_single]
  split_ifs <;> simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]

open Classical in
private theorem localCoeff_apply (A : AffineSubspace ℝ V) (f : Fin k → V) (q : V)
    (x : OrientedCell h k →₀ E) :
    localCoeff (R := R) A f q x = ∑ σ ∈ x.support,
      if affineSpan ℝ σ.carrier = A ∧ q ∈ σ.carrier then (σ.orientation.evalSign f : ℤ) • x σ
      else 0 := by
  rw [localCoeff, Finsupp.lsum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]

/-- The formal sums whose local coefficient along `A` vanishes off a nowhere dense subset
of `A`. -/
private def locallyNull (A : AffineSubspace ℝ V) (f : Fin k → V) :
    Submodule R (OrientedCell h k →₀ E) where
  carrier := {z | ∃ S : Set A, IsNowhereDense S ∧ ∀ q : A, q ∉ S → localCoeff A f q z = 0}
  zero_mem' := ⟨∅, isNowhereDense_empty, fun _ _ => map_zero _⟩
  add_mem' := by
    rintro x y ⟨S, hS, hx⟩ ⟨T, hT, hy⟩
    refine ⟨S ∪ T, hS.union hT, fun q hq => ?_⟩
    rw [map_add, hx q fun h => hq (Or.inl h), hy q fun h => hq (Or.inr h), add_zero]
  smul_mem' := by
    rintro r x ⟨S, hS, hx⟩
    exact ⟨S, hS, fun q hq => by rw [map_smul, hx q hq, smul_zero]⟩

private theorem localCoeff_single_of_mem {A : AffineSubspace ℝ V} {f : Fin k → V} {q : V}
    {τ : OrientedCell h k} (hA : affineSpan ℝ τ.carrier = A) (hq : q ∈ τ.carrier) (c : E) :
    localCoeff (R := R) A f q (Finsupp.single τ c) = (τ.orientation.evalSign f : ℤ) • c := by
  rw [localCoeff_single, ite_eq_left ⟨hA, hq⟩]

private theorem localCoeff_single_of_not {A : AffineSubspace ℝ V} {f : Fin k → V} {q : V}
    {τ : OrientedCell h k} (hτ : ¬(affineSpan ℝ τ.carrier = A ∧ q ∈ τ.carrier)) (c : E) :
    localCoeff (R := R) A f q (Finsupp.single τ c) = 0 := by
  rw [localCoeff_single, ite_eq_right hτ]

/-- Every cochain relation has vanishing local coefficients off a nowhere dense set: a reversal
relation vanishes everywhere, and a subdivision relation vanishes off the relative boundaries of
the pieces. -/
private theorem cochainRelations_le_locallyNull (A : AffineSubspace ℝ V) (f : Fin k → V) :
    cochainRelations R h E k ≤ locallyNull (R := R) A f := by
  refine cochainRelations_le_iff.mpr ⟨fun σ c => ?_, fun σ Q c hQ => ?_⟩
  · refine ⟨∅, isNowhereDense_empty, fun q _ => ?_⟩
    rw [map_add]
    by_cases hc : affineSpan ℝ σ.carrier = A ∧ (q : V) ∈ σ.carrier
    · rw [localCoeff_single_of_mem (by rw [reverse_carrier]; exact hc.1)
          (by rw [reverse_carrier]; exact hc.2),
        localCoeff_single_of_mem hc.1 hc.2, reverse_orientation, Module.Ray.evalSign_neg,
        SignType.coe_neg, neg_smul, neg_add_cancel]
    · rw [localCoeff_single_of_not (by rwa [reverse_carrier]), localCoeff_single_of_not hc,
        add_zero]
  by_cases hσA : affineSpan ℝ σ.carrier = A
  · have hτA {τ : OrientedCell h k} (hτ : τ ∈ Q) : affineSpan ℝ τ.carrier = A :=
      (hQ.affineSpan_eq hτ).trans hσA
    have hS : IsNowhereDense (⋃ τ ∈ Q, ((↑) ⁻¹' intrinsicFrontier ℝ τ.carrier : Set A)) :=
      IsNowhereDense.biUnion fun τ hτ =>
        isNowhereDense_preimage_intrinsicFrontier τ.isClosed_carrier (hτA hτ)
    refine ⟨_, hS, fun q hq => ?_⟩
    simp only [mem_iUnion, mem_preimage, not_exists] at hq
    rw [map_sub, map_sum, sub_eq_zero]
    by_cases hqσ : (q : V) ∈ σ.carrier
    · -- Exactly one piece contains `q`, since `q` is off the relative boundaries of the pieces.
      have hqQ := hqσ
      rw [← hQ.biUnion_carrier, mem_iUnion₂] at hqQ
      obtain ⟨τ₀, hτ₀, hqτ₀⟩ := hqQ
      have hint {τ : OrientedCell h k} (hτ : τ ∈ Q) (hqτ : (q : V) ∈ τ.carrier) :
          (q : V) ∈ intrinsicInterior ℝ τ.carrier := by
        rw [← intrinsicClosure_sdiff_intrinsicFrontier]
        exact ⟨subset_intrinsicClosure hqτ, hq τ hτ⟩
      rw [Finset.sum_eq_single τ₀ (fun τ hτ hne => localCoeff_single_of_not (fun hc =>
          (hQ.pairwiseDisjoint hτ hτ₀ hne).ne_of_mem (hint hτ hc.2) (hint hτ₀ hqτ₀) rfl) c)
          (fun h => (h hτ₀).elim),
        localCoeff_single_of_mem hσA hqσ, localCoeff_single_of_mem (hτA hτ₀) hqτ₀,
        hQ.orientation_eq τ₀ hτ₀]
    · rw [localCoeff_single_of_not (fun hc => hqσ hc.2), eq_comm]
      exact Finset.sum_eq_zero fun τ hτ =>
        localCoeff_single_of_not (fun hc => hqσ (hQ.carrier_subset hτ hc.2)) c
  · refine ⟨∅, isNowhereDense_empty, fun q _ => ?_⟩
    rw [map_sub, map_sum, localCoeff_single_of_not fun hc => hσA hc.1, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun τ hτ =>
      localCoeff_single_of_not (fun hc => hσA ((hQ.affineSpan_eq hτ).symm.trans hc.1)) c

/-- A cochain relation has zero local coefficient at every point `q` of `A` off the relative
boundaries of its cells: the local coefficient is constant near `q` in `A`, and vanishes off a
nowhere dense subset of `A`. -/
private theorem localCoeff_eq_zero {z : OrientedCell h k →₀ E}
    (hz : z ∈ cochainRelations R h E k) (A : AffineSubspace ℝ V) (f : Fin k → V) (q : A)
    (hq : ∀ σ ∈ z.support, (q : V) ∉ intrinsicFrontier ℝ σ.carrier) :
    localCoeff (R := R) A f q z = 0 := by
  classical
  obtain ⟨S, hS, hzS⟩ := cochainRelations_le_locallyNull A f hz
  have hmem : ∀ᶠ y : A in 𝓝 q, ∀ σ ∈ z.support,
      affineSpan ℝ σ.carrier = A → ((y : V) ∈ σ.carrier ↔ (q : V) ∈ σ.carrier) := by
    rw [Filter.eventually_all_finset]
    intro σ hσ
    by_cases hσA : affineSpan ℝ σ.carrier = A
    · filter_upwards [eventually_mem_iff_of_notMem_intrinsicFrontier σ.isClosed_carrier hσA
        (hq σ hσ)] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun y hA => absurd hA hσA
  have hev : ∀ᶠ y : A in 𝓝 q, localCoeff (R := R) A f y z = localCoeff (R := R) A f q z := by
    filter_upwards [hmem] with y hy
    rw [localCoeff_apply, localCoeff_apply]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    by_cases hσA : affineSpan ℝ σ.carrier = A
    · rw [hy σ hσ hσA]
    · simp [hσA]
  have hdense : Dense Sᶜ := (interior_eq_empty_iff_dense_compl.mp hS).mono
    (compl_subset_compl.mpr subset_closure)
  obtain ⟨y, hyS, hy⟩ := hdense.inter_nhds_nonempty hev
  rw [← hy, hzS y hyS]

end relations

/-- A cochain relation pairs to zero with every test transverse to all of its cells, although
the relation may be generated by cells to which the test is not transverse. -/
theorem intersectionPairing_eq_zero_of_mem_cochainRelations {v : Fin (k + 1) → V}
    {z : OrientedCell h k →₀ E} (hz : z ∈ cochainRelations R h E k)
    (hv : ∀ σ ∈ z.support, σ.IsTransverse v) :
    intersectionPairing (R := R) v z = 0 := by
  classical
  -- Group the cells by affine span.
  rw [intersectionPairing_apply, Finsupp.sum,
    ← Finset.sum_fiberwise_of_maps_to (g := fun σ => affineSpan ℝ σ.carrier)
      (t := z.support.image fun σ => affineSpan ℝ σ.carrier)
      fun σ hσ => Finset.mem_image_of_mem _ hσ]
  refine Finset.sum_eq_zero fun A _ => ?_
  by_cases hmeet : ∃ σ ∈ z.support, affineSpan ℝ σ.carrier = A ∧
      (convexHull ℝ (range v) ∩ σ.carrier).Nonempty
  · -- The test meets `A` in a single point `q`, so the group is the local coefficient at `q`.
    obtain ⟨σ₀, hσ₀, hσ₀A, q, hqv, hqσ₀⟩ := hmeet
    have hsub := (hv σ₀ hσ₀).subsingleton_convexHull_inter_affineSpan ⟨q, hqv, hqσ₀⟩
    rw [hσ₀A] at hsub
    have hqA : q ∈ A := hσ₀A ▸ subset_affineSpan ℝ _ hqσ₀
    have hgroup : ∑ σ ∈ z.support with affineSpan ℝ σ.carrier = A,
        σ.intersectionIndex v • z σ =
          localCoeff (R := R) A (fun j : Fin k => v j.succ - v 0) q z := by
      rw [localCoeff_apply, Finset.sum_filter]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases hσA : affineSpan ℝ σ.carrier = A
      · have hiff : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty ↔ q ∈ σ.carrier := by
          refine ⟨fun ⟨p, hpv, hpσ⟩ => ?_, fun hq => ⟨q, hqv, hq⟩⟩
          rwa [hsub ⟨hpv, hσA ▸ subset_affineSpan ℝ _ hpσ⟩ ⟨hqv, hqA⟩] at hpσ
        rw [ite_eq_left hσA]
        by_cases hqσ : q ∈ σ.carrier
        · rw [ite_eq_left ⟨hσA, hqσ⟩, intersectionIndex_of_nonempty (hiff.mpr hqσ)]
        · rw [ite_eq_right fun hc => hqσ hc.2, intersectionIndex_of_disjoint
            (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp (hiff.not.mpr hqσ))),
            zero_smul]
      · rw [ite_eq_right hσA, ite_eq_right fun hc => hσA hc.1]
    rw [hgroup]
    exact localCoeff_eq_zero hz A _ ⟨q, hqA⟩ fun σ hσ =>
      (hv σ hσ).disjoint_intrinsicFrontier.notMem_of_mem_left hqv
  · -- The test misses every cell of the group.
    simp only [not_exists, not_and] at hmeet
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [intersectionIndex_of_disjoint (disjoint_iff_inter_eq_empty.mpr
      (not_nonempty_iff_eq_empty.mp (hmeet σ hσ.1 hσ.2))), zero_smul]

end OrientedCell

namespace PolyhedralCochain

open OrientedCell

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

/-- The cochain relations preserve the intersection pairing whenever the test is transverse to
both representatives: two formal sums representing the same cochain have the same pairing with
every test transverse to all of their cells. -/
theorem intersectionPairing_eq_of_ofFinsupp_eq {v : Fin (k + 1) → V}
    {x y : OrientedCell h k →₀ E} (hxy : ofFinsupp (R := R) x = ofFinsupp y)
    (hx : ∀ σ ∈ x.support, σ.IsTransverse v) (hy : ∀ σ ∈ y.support, σ.IsTransverse v) :
    intersectionPairing (R := R) v x = intersectionPairing (R := R) v y := by
  classical
  rw [← sub_eq_zero, ← map_sub]
  refine intersectionPairing_eq_zero_of_mem_cochainRelations ?_ fun σ hσ => ?_
  · rw [← ofFinsupp_eq_zero_iff, map_sub, hxy, sub_self]
  · rcases Finset.mem_union.mp (Finsupp.support_sub hσ) with hσ | hσ
    exacts [hx σ hσ, hy σ hσ]

end PolyhedralCochain

end Mei
