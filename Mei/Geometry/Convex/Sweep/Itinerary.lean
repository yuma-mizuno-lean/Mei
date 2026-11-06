/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Intrinsic
public import Mei.Geometry.Convex.Sweep.Topology
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Backward affine propagation along a fixed itinerary

Starting at an endpoint, propagate backwards along specified vectors toward
specified hyperplanes. The propagation points and times are continuous affine
functions of the endpoint, obtained by composing the existing `sweepProjection`
maps. A step is an actual hyperplane encounter when `f i (v i) ≠ 0`; this
transversality also gives uniqueness, without a genericity assumption. When
`f i (v i) = 0`, the totalized formulas assign zero time and leave the point
unchanged, which may lie outside the selected hyperplane.

The vectors point backwards along the itinerary. For a broken line with forward
velocity `-ρ(p)`, use `ρ(p)` here; positive elapsed times impose the correct order.
The sign of the normal applied to the velocity may be negative. Incidence with
the selected supports does not assert that a segment avoids other walls or meets
a selected wall for the first time.

Positive elapsed times and relative-interior encounters persist near the endpoint
when each support's affine direction contains the kernel of its normal. No
supporting-hyperplane containment or surjectivity of the encounter maps is required.
A boundary endpoint therefore has a zero elapsed time or an encounter on a
relative support boundary, even for nonclosed supports. We use relative-interior
neighborhoods in affine spans to establish this persistence.
The endpoint-chart interpretation follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

noncomputable section

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → V)

/-- Backward propagation points as affine functions of the endpoint. A transverse
step encounters its selected hyperplane; a tangent step leaves its point unchanged.
Index zero is the endpoint. -/
def backwardPoint : Fin (n + 1) → (V →ᴬ[ℝ] V) :=
  Fin.induction (ContinuousAffineMap.id ℝ V)
    (fun i X => (sweepProjection (f i) (c i) ((f i (v i))⁻¹ • v i)).comp X)

/-- The starting point of backward propagation is the endpoint. -/
@[simp]
theorem backwardPoint_zero : backwardPoint f c v 0 = ContinuousAffineMap.id ℝ V := by
  simp only [backwardPoint, Fin.induction_zero]

/-- Each propagation step uses the normalized sweep; a tangent step is the identity. -/
theorem backwardPoint_succ (i : Fin n) :
    backwardPoint f c v i.succ =
      (sweepProjection (f i) (c i) ((f i (v i))⁻¹ • v i)).comp
        (backwardPoint f c v i.castSucc) := by
  simp only [backwardPoint, Fin.induction_succ]

/-- The backward-time formula, zero at tangent steps. At a transverse step this is
the physical elapsed time to the next selected hyperplane; its positivity orders
the encounters independently of the sign of the unnormalized height difference. -/
def backwardTime (i : Fin n) : V →ᴬ[ℝ] ℝ :=
  (f i (v i))⁻¹ • (ContinuousAffineMap.const ℝ V (c i) -
    (f i).toContinuousAffineMap.comp (backwardPoint f c v i.castSucc))

/-- The linear part of elapsed time is the negative pulled-back normal divided
by its value on the velocity. -/
@[simp]
theorem backwardTime_linear (j : Fin n) :
    (backwardTime f c v j).toAffineMap.linear =
      (f j (v j))⁻¹ • (-(f j).toLinearMap.comp
        (backwardPoint f c v j.castSucc).toAffineMap.linear) := by
  ext x
  simp [backwardTime, ← ContinuousAffineMap.coe_contLinear]

/-- The affine backward-time formula. -/
@[simp]
theorem backwardTime_apply (i : Fin n) (Q : V) :
    backwardTime f c v i Q =
      (c i - f i (backwardPoint f c v i.castSucc Q)) / f i (v i) := by
  simp only [backwardTime, ContinuousAffineMap.smul_apply, ContinuousAffineMap.sub_apply,
    ContinuousAffineMap.coe_const, Function.const_apply, ContinuousAffineMap.comp_apply,
    ContinuousLinearMap.coe_toContinuousAffineMap, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Successive propagation points differ by the backward-time formula times the
specified velocity, including tangent steps with zero time. -/
@[simp]
theorem backwardPoint_succ_apply (i : Fin n) (Q : V) :
    backwardPoint f c v i.succ Q = backwardPoint f c v i.castSucc Q +
      backwardTime f c v i Q • v i := by
  rw [backwardPoint_succ, ContinuousAffineMap.comp_apply, sweepProjection_apply,
    backwardTime_apply, smul_smul, div_eq_mul_inv]

/-- A transverse step lies on its selected hyperplane. -/
theorem backwardPoint_height (i : Fin n) (hi : f i (v i) ≠ 0) (Q : V) :
    f i (backwardPoint f c v i.succ Q) = c i := by
  rw [backwardPoint_succ, ContinuousAffineMap.comp_apply]
  apply sweepProjection_height
  simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hi]

/-- Endpoint, velocities and transverse hyperplanes uniquely determine every
encounter and elapsed time. Positivity is unnecessary for this uniqueness law. -/
theorem backward_unique (hf : ∀ i, f i (v i) ≠ 0) (Q : V)
    (X : Fin (n + 1) → V) (t : Fin n → ℝ) (hX : X 0 = Q)
    (hstep : ∀ i, X i.succ = X i.castSucc + t i • v i)
    (hheight : ∀ i, f i (X i.succ) = c i) :
    (∀ i, X i = backwardPoint f c v i Q) ∧
      ∀ i, t i = backwardTime f c v i Q := by
  have htime (i : Fin n) : t i = (c i - f i (X i.castSucc)) / f i (v i) := by
    apply (eq_div_iff (hf i)).mpr
    have h := hheight i
    rw [hstep i, map_add, map_smul, smul_eq_mul] at h
    linarith
  have hp : ∀ i, X i = backwardPoint f c v i Q := by
    intro i
    induction i using Fin.induction with
    | zero => simpa only [backwardPoint_zero, ContinuousAffineMap.coe_id, id_eq] using hX
    | succ i ih =>
      rw [hstep, backwardPoint_succ_apply, htime, ih, backwardTime_apply]
  exact ⟨hp, fun i => by rw [htime, backwardTime_apply, hp]⟩

/-- Rescaling each normal and its level by the same nonzero scalar preserves
all propagation points and time formulas, including tangent steps and negative scalars. -/
theorem backward_rescale (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (Q : V) :
    (∀ i, backwardPoint (fun j => a j • f j) (fun j => a j * c j) v i Q =
      backwardPoint f c v i Q) ∧
    ∀ i, backwardTime (fun j => a j • f j) (fun j => a j * c j) v i Q =
      backwardTime f c v i Q := by
  have ht (i : Fin n)
      (hi : backwardPoint (fun j => a j • f j) (fun j => a j * c j) v i.castSucc Q =
        backwardPoint f c v i.castSucc Q) :
      backwardTime (fun j => a j • f j) (fun j => a j * c j) v i Q =
        backwardTime f c v i Q := by
    rw [backwardTime_apply, backwardTime_apply, hi]
    simp only [smul_apply, smul_eq_mul, ← mul_sub]
    exact mul_div_mul_left _ _ (ha i)
  have hp : ∀ i, backwardPoint (fun j => a j • f j) (fun j => a j * c j) v i Q =
      backwardPoint f c v i Q := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ i ih => rw [backwardPoint_succ_apply, backwardPoint_succ_apply, ht i ih, ih]
  exact ⟨hp, fun i => ht i (hp i.castSucc)⟩


/-- Endpoints satisfying the selected support incidences and strictly positive
backward elapsed times. -/
def backwardDomain (P : Fin n → Set V) : Set V :=
  {Q | ∀ i, 0 < backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i}

/-- The weakened endpoint constraints, allowing zero elapsed times. -/
def weakBackwardDomain (P : Fin n → Set V) : Set V :=
  {Q | ∀ i, 0 ≤ backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i}

/-- Membership in the strict endpoint domain. -/
@[simp]
theorem mem_backwardDomain (P : Fin n → Set V) (Q : V) :
    Q ∈ backwardDomain f c v P ↔
      ∀ i, 0 < backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i := Iff.rfl

/-- Membership in the weak endpoint domain. -/
@[simp]
theorem mem_weakBackwardDomain (P : Fin n → Set V) (Q : V) :
    Q ∈ weakBackwardDomain f c v P ↔
      ∀ i, 0 ≤ backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i := Iff.rfl

/-- Strict endpoint constraints imply the weakened ones. -/
theorem backwardDomain_subset_weakBackwardDomain (P : Fin n → Set V) :
    backwardDomain f c v P ⊆ weakBackwardDomain f c v P :=
  fun _ h i => ⟨(h i).1.le, (h i).2⟩

section

variable {ι : Type*} (u : Fin n → V) (W : ι → Set V) (wall : Fin n → ι)
  (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)

include hheight

/-- Consecutive encounters of a strict itinerary have different affine spans,
even when the itinerary uses repeated wall indices. -/
theorem affineSpan_ne_of_mem_backwardDomain {Q : V}
    (hQ : Q ∈ backwardDomain f c u (fun j => W (wall j)))
    {i j : Fin n} (hij : i.succ = j.castSucc) :
    affineSpan ℝ (W (wall i)) ≠ affineSpan ℝ (W (wall j)) := by
  have hm := (mem_backwardDomain f c u _ Q).mp hQ
  intro he
  have hx : backwardPoint f c u j.castSucc Q ∈ affineSpan ℝ (W (wall j)) := by
    rw [← hij, ← he]
    exact subset_affineSpan ℝ _ (hm i).2
  have hspan := AffineMap.eqOn_affineSpan
    (f := (f j).toLinearMap.toAffineMap) (g := AffineMap.const ℝ V (c j))
    (hheight j)
  have hval : f j (backwardPoint f c u j.castSucc Q) = c j := by
    simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe,
      AffineMap.const_apply] using hspan hx
  have hz : backwardTime f c u j Q = 0 := by
    rw [backwardTime_apply, hval, sub_self, zero_div]
  exact (ne_of_gt (hm j).1) hz

end

/-- Convex support constraints give a convex strict endpoint domain. -/
theorem convex_backwardDomain {P : Fin n → Set V} (hP : ∀ i, Convex ℝ (P i)) :
    Convex ℝ (backwardDomain f c v P) := by
  have he : backwardDomain f c v P = ⋂ i,
      (backwardTime f c v i) ⁻¹' Set.Ioi 0 ∩
        (backwardPoint f c v i.succ) ⁻¹' P i := by
    ext Q
    simp only [mem_backwardDomain, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ioi]
  rw [he]
  exact convex_iInter fun i =>
    ((convex_Ioi (0 : ℝ)).affine_preimage (backwardTime f c v i).toAffineMap).inter
      ((hP i).affine_preimage (backwardPoint f c v i.succ).toAffineMap)

/-- Convex support constraints give a convex weak endpoint domain, even when
no strict endpoint exists. -/
theorem convex_weakBackwardDomain {P : Fin n → Set V} (hP : ∀ i, Convex ℝ (P i)) :
    Convex ℝ (weakBackwardDomain f c v P) := by
  have he : weakBackwardDomain f c v P = ⋂ i,
      (backwardTime f c v i) ⁻¹' Set.Ici 0 ∩
        (backwardPoint f c v i.succ) ⁻¹' P i := by
    ext Q
    simp only [mem_weakBackwardDomain, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici]
  rw [he]
  exact convex_iInter fun i =>
    ((convex_Ici (0 : ℝ)).affine_preimage (backwardTime f c v i).toAffineMap).inter
      ((hP i).affine_preimage (backwardPoint f c v i.succ).toAffineMap)

/-- Closed support constraints give a closed weak endpoint domain. -/
theorem isClosed_weakBackwardDomain {P : Fin n → Set V} (hP : ∀ i, IsClosed (P i)) :
    IsClosed (weakBackwardDomain f c v P) := by
  have he : weakBackwardDomain f c v P = ⋂ i,
      (backwardTime f c v i) ⁻¹' Set.Ici 0 ∩
        (backwardPoint f c v i.succ) ⁻¹' P i := by
    ext Q
    simp only [mem_weakBackwardDomain, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici]
  rw [he]
  exact isClosed_iInter fun i =>
    (isClosed_Ici.preimage (backwardTime f c v i).continuous).inter
      ((hP i).preimage (backwardPoint f c v i.succ).continuous)

/-- Elapsed times remain nonnegative on the closure of any endpoint family
with nonnegative elapsed times, without support constraints. -/
theorem backwardTime_nonneg_of_mem_closure {D : Set V}
    (hD : ∀ Q ∈ D, ∀ j, 0 ≤ backwardTime f c v j Q)
    {Q : V} (hQ : Q ∈ closure D) (j : Fin n) :
    0 ≤ backwardTime f c v j Q := by
  apply closure_minimal (s := D)
    (t := (backwardTime f c v j) ⁻¹' Set.Ici 0) _
    (isClosed_Ici.preimage (backwardTime f c v j).continuous) hQ
  intro Q hQ
  exact hD Q hQ j

/-- A positive backward elapsed time forces the corresponding wall functional to be
nonzero on the direction. -/
theorem ne_zero_of_backwardTime_pos {j : Fin n} {Q : V} (ht : 0 < backwardTime f c v j Q) :
    f j (v j) ≠ 0 := by
  intro hz
  simp only [backwardTime_apply, hz, div_zero] at ht
  exact (lt_irrefl 0) ht

section DomainInterior

open Set Filter Topology

variable (P : Fin n → Set V)
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (P j)).direction)

include hdir

/-- For a transverse wall, once one encounter lies in the affine span of the support,
every encounter does: the encounter map is constant along the kernel direction. -/
theorem backwardPoint_succ_mem_affineSpan {j : Fin n} (hf : f j (v j) ≠ 0) {X Y : V}
    (hY : backwardPoint f c v j.succ Y ∈ affineSpan ℝ (P j)) :
    backwardPoint f c v j.succ X ∈ affineSpan ℝ (P j) := by
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hY]
  apply hdir j
  rw [LinearMap.mem_ker, vsub_eq_sub, map_sub]
  simp only [ContinuousLinearMap.coe_coe]
  rw [backwardPoint_height f c v j hf X, backwardPoint_height f c v j hf Y, sub_self]

/-- Strict time order and relative-interior wall encounters persist near the
endpoint. No convexity, closedness or finite-dimensionality is required. -/
theorem mem_interior_backwardDomain {Q : V}
    (ht : ∀ j, 0 < backwardTime f c v j Q)
    (hP : ∀ j, backwardPoint f c v j.succ Q ∈ intrinsicInterior ℝ (P j)) :
    Q ∈ interior (backwardDomain f c v P) := by
  apply mem_interior_iff_mem_nhds.mpr
  suffices he : ∀ᶠ X in 𝓝 Q, ∀ j,
      0 < backwardTime f c v j X ∧ backwardPoint f c v j.succ X ∈ P j by
    exact he.mono fun X hX => (mem_backwardDomain f c v P X).mpr hX
  apply eventually_all.mpr
  intro j
  have hf := ne_zero_of_backwardTime_pos f c v (ht j)
  have hspan (X : V) : backwardPoint f c v j.succ X ∈ affineSpan ℝ (P j) :=
    backwardPoint_succ_mem_affineSpan f c v P hdir hf
      (subset_affineSpan ℝ _ (intrinsicInterior_subset (hP j)))
  have hlim := tendsto_nhdsWithin_iff.mpr
    ⟨(backwardPoint f c v j.succ).continuous.tendsto Q, Eventually.of_forall hspan⟩
  exact ((backwardTime f c v j).continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (ht j))).and
      (hlim.eventually (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior (hP j)))

/-- At a boundary of the selected-incidence domain, some elapsed time vanishes
or a selected encounter lies on its wall's relative boundary. The converse can
fail when an encounter map has smaller rank. -/
theorem mem_frontier_backwardDomain_imp_time_eq_zero_or_mem_intrinsicFrontier
    {Q : V} (hQ : Q ∈ frontier (backwardDomain f c v P)) :
    (∃ j, backwardTime f c v j Q = 0) ∨
      ∃ j, backwardPoint f c v j.succ Q ∈ intrinsicFrontier ℝ (P j) := by
  by_contra! hnone
  have ht (j) : 0 < backwardTime f c v j Q :=
    lt_of_le_of_ne (backwardTime_nonneg_of_mem_closure f c v
      (fun X hX i => (hX i).1.le) hQ.1 j) (Ne.symm (hnone.1 j))
  obtain ⟨p, hp⟩ := (Set.nonempty_of_mem hQ.1).of_closure
  have hi (j) : backwardPoint f c v j.succ Q ∈ intrinsicInterior ℝ (P j) := by
    have hspan : backwardPoint f c v j.succ Q ∈ affineSpan ℝ (P j) :=
      backwardPoint_succ_mem_affineSpan f c v P hdir
        (ne_zero_of_backwardTime_pos f c v (ht j)) (subset_affineSpan ℝ _ (hp j).2)
    have hcl : backwardPoint f c v j.succ Q ∈ closure (P j) :=
      closure_mono (Set.image_subset_iff.mpr fun X hX => (hX j).2)
        (mem_closure_image (backwardPoint f c v j.succ).continuous.continuousAt hQ.1)
    rw [← intrinsicClosure_sdiff_intrinsicFrontier]
    refine ⟨?_, hnone.2 j⟩
    rw [intrinsicClosure_eq_closure_inter_affineSpan]
    exact ⟨hcl, hspan⟩
  exact hQ.2 (mem_interior_backwardDomain f c v P hdir ht hi)

end DomainInterior

/-- Locally closed support constraints give a locally closed strict endpoint domain. -/
theorem isLocallyClosed_backwardDomain {P : Fin n → Set V}
    (hP : ∀ i, IsLocallyClosed (P i)) : IsLocallyClosed (backwardDomain f c v P) := by
  classical
  choose U Z hU hZ he using fun i =>
    (hP i).preimage (backwardPoint f c v i.succ).continuous
  have hd : backwardDomain f c v P =
      (⋂ i, (backwardTime f c v i) ⁻¹' Set.Ioi 0 ∩ U i) ∩ ⋂ i, Z i := by
    ext Q
    simp only [mem_backwardDomain, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      have hm (i) : Q ∈ U i ∩ Z i := by rw [← he i]; exact (h i).2
      exact ⟨fun i => ⟨(h i).1, (hm i).1⟩, fun i => (hm i).2⟩
    · rintro ⟨h, hz⟩ i
      refine ⟨(h i).1, ?_⟩
      have hm : Q ∈ U i ∩ Z i := ⟨(h i).2, hz i⟩
      rwa [← he i] at hm
  rw [hd]
  exact (isOpen_iInter_of_finite fun i =>
    (isOpen_Ioi.preimage (backwardTime f c v i).continuous).inter (hU i)).isLocallyClosed.inter
      (isClosed_iInter hZ).isLocallyClosed

section EndpointConditions

variable {m : Fin n → ℕ} (g : ∀ i, Fin (m i) → V →ᴬ[ℝ] ℝ)

/-- Affine endpoint conditions: negative elapsed times, followed by support
inequalities pulled back to the respective encounter points. -/
def backwardCondition : (Fin n ⊕ (Σ i, Fin (m i))) → V →ᴬ[ℝ] ℝ :=
  Sum.elim (fun i => -backwardTime f c v i)
    (fun j => (g j.1 j.2).comp (backwardPoint f c v j.1.succ))

/-- The time row is nonpositive exactly when the elapsed time is nonnegative. -/
@[simp]
theorem backwardCondition_time (i : Fin n) (Q : V) :
    backwardCondition f c v g (.inl i) Q = -backwardTime f c v i Q := (rfl)

/-- The support row is evaluated at the corresponding encounter point. -/
@[simp]
theorem backwardCondition_support (i : Fin n) (j : Fin (m i)) (Q : V) :
    backwardCondition f c v g (.inr ⟨i, j⟩) Q =
      g i j (backwardPoint f c v i.succ Q) := (rfl)

end EndpointConditions

/-- Polyhedral support constraints pull back to a polyhedron when zero elapsed
times are admitted. No boundedness or finite-dimensionality is assumed. -/
theorem isConvexPolyhedron_weakBackwardDomain {P : Fin n → Set V}
    (hP : ∀ i, TauCeti.IsConvexPolyhedron (P i)) :
    TauCeti.IsConvexPolyhedron (weakBackwardDomain f c v P) := by
  choose m g hg using fun i => TauCeti.isConvexPolyhedron_iff.mp (hP i)
  have he : weakBackwardDomain f c v P =
      {Q | ∀ j, backwardCondition f c v g j Q ≤ 0} := by
    ext Q
    simp only [mem_weakBackwardDomain, hg, Set.mem_ofPred_eq, backwardCondition, Sum.forall,
      Sum.elim_inl, Sum.elim_inr,
      Sigma.forall, ContinuousAffineMap.neg_apply, neg_nonpos,
      ContinuousAffineMap.comp_apply, forall_and]
  rw [he]
  exact TauCeti.isConvexPolyhedron_setOf_forall (backwardCondition f c v g)

/-- If one strict realization exists, every weak realization is its limit along
a segment inside the support constraints. The nonemptiness hypothesis is essential. -/
theorem closure_backwardDomain {P : Fin n → Set V}
    (hclosed : ∀ i, IsClosed (P i)) (hconvex : ∀ i, Convex ℝ (P i))
    (hne : (backwardDomain f c v P).Nonempty) :
    closure (backwardDomain f c v P) = weakBackwardDomain f c v P := by
  apply Set.Subset.antisymm
  · exact closure_minimal (backwardDomain_subset_weakBackwardDomain f c v P)
      (isClosed_weakBackwardDomain f c v hclosed)
  · obtain ⟨p, hp⟩ := hne
    intro x hx
    have hs : openSegment ℝ x p ⊆ backwardDomain f c v P := by
      rintro y ⟨a, b, ha, hb, hab, rfl⟩ i
      constructor
      · have he : backwardTime f c v i (a • x + b • p) =
            a * backwardTime f c v i x + b * backwardTime f c v i p :=
          Convex.combo_affine_apply (f := (backwardTime f c v i).toAffineMap) hab
        rw [he]
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hx i).1) (mul_pos hb (hp i).1)
      · have he : backwardPoint f c v i.succ (a • x + b • p) =
            a • backwardPoint f c v i.succ x + b • backwardPoint f c v i.succ p :=
          Convex.combo_affine_apply (f := (backwardPoint f c v i.succ).toAffineMap) hab
        rw [he]
        exact hconvex i (hx i).2 (hp i).2 ha.le hb.le hab
    exact closure_mono hs
      (segment_subset_closure_openSegment (left_mem_segment ℝ x p))

end Mei.Convex
