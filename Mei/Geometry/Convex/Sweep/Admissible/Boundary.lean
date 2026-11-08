/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Regular
public import Mei.Geometry.Convex.Sweep.Admissible.Source
public import Mei.Geometry.Convex.Sweep.Boundary
public import Mei.Geometry.Convex.Sweep.Singular.Stability

/-!
# Boundaries of admissible backward domains

Fix the directions, selected supports, walls, singular sets and incoming source
of a backward ray. At a limit of admissible endpoints, every recorded encounter
stays in the closure of its selected support. Every frontier point of the
admissible domain is a boundary of the remaining constraints or a genuine
singular contact of the extended negative half-line.

Suppose the walls and singular sets are convex polyhedra and recorded
encounters preserve normal velocity. At a regular limit, whose endpoint misses
the walls and whose negative half-line misses both wall singular support and the
singular sets, selected incidence, strict time order, absence of unrecorded
contacts and singular avoidance all persist on a neighborhood. Selected supports
may be nonclosed provided they agree locally with their ambient walls at regular
limits; exact simultaneous-event supports have this property. The admissible
domain then agrees locally with the domain of admitted incoming tails.

Consequently a frontier endpoint is terminal, has an actual singular contact,
or has its incoming tail in a tight tangential source face whose inequality
varies with the endpoint. For closed selected supports and a convex polyhedral
source, a regular limit is admissible. Neither codimensions of the boundary
events nor admissibility of singular boundary paths is asserted.

These statements concern the backward path family itself and apply to every
broken-line carrier whose type paths are backward paths. The closed-family
interpretation follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V K O : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V)
  (W : O → Set V) (S : K → Set V) (C : Set V)

local notation "D" => admissibleBackwardDomain f c v P W S C
local notation "u" => fun j : Fin n => v (Fin.castSucc j)
local notation "τ" => backwardParameter f c (fun j : Fin n => v (Fin.castSucc j))
local notation "X" => backwardPoint f c (fun j : Fin n => v (Fin.castSucc j))

/-- At a limiting endpoint, each recorded encounter stays in the closure of its
selected support, including nonclosed exact simultaneous-event supports. -/
theorem backwardPoint_succ_mem_closure_of_mem_closure
    {Q : V} (hQ : Q ∈ closure D) (j : Fin n) : X j.succ Q ∈ closure (P j) :=
  Set.MapsTo.closure (fun _ hY => (((mem_backwardDomain ..).mp
    (admissibleBackwardDomain_subset_backwardDomain _ _ _ _ _ _ _ hY)) j).2)
    (X j.succ).continuous hQ

/-- Every recorded encounter of a limiting endpoint remains on its closed selected
support, even when its time coincides with another encounter or the endpoint. -/
theorem backwardPoint_succ_mem_of_mem_closure (hP : ∀ j, IsClosed (P j))
    {Q : V} (hQ : Q ∈ closure D) (j : Fin n) : X j.succ Q ∈ P j :=
  (hP j).closure_subset (backwardPoint_succ_mem_closure_of_mem_closure f c v P W S C hQ j)

section Support

variable {ι : Type*} (A : ι → Set V) (wall : Fin n → ι)
  (hclosed : ∀ i, IsClosed (A i)) (hP : ∀ j, P j ⊆ A (wall j))
  (hheight : ∀ j x, x ∈ A (wall j) → f j x = c j)
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (A (wall j))).direction)

include hclosed hP hheight hdir

/-- At a regular limiting endpoint, the strict ambient-wall incidence
constraints hold throughout a neighborhood. This says nothing about new
unrecorded encounters or admission to the incoming source at nearby endpoints. -/
theorem mem_interior_backwardDomain_of_regular_limit
    {Q : V} (hQ : Q ∈ closure D) (hendpoint : ∀ i, Q ∉ A i)
    (hregular : ∀ j : Fin n, X j.succ Q ∉ singularSupport A) :
    Q ∈ interior (backwardDomain f c u fun j => A (wall j)) := by
  by_contra hi
  have hb : Q ∈ frontier (backwardDomain f c u fun j => A (wall j)) :=
    ⟨closure_mono (admissibleBackwardDomain_subset_backwardDomain_of_subset
      f c v P W S C hP) hQ, hi⟩
  rcases mem_frontier_backwardDomain_imp_terminal_or_singularSupport f c u A wall hheight
    hdir hclosed hb with ⟨j, _, hj⟩ | ⟨j, hj⟩
  · exact hendpoint _ (by simpa only [backwardPoint_succ_apply] using hj)
  · exact hregular j hj

/-- Nonclosed selected supports have no additional regular incidence boundary
when their germs at regular limits agree with their ambient walls. This applies
to exact simultaneous events, whose omitted wall indices must also persist. -/
theorem mem_interior_backwardDomain_of_regular_limit_of_eventually_mem
    (hlocal : ∀ j x, x ∈ closure (P j) → x ∉ singularSupport A →
      ∀ᶠ y in 𝓝 x, y ∈ A (wall j) → y ∈ P j)
    {Q : V} (hQ : Q ∈ closure D) (hendpoint : ∀ i, Q ∉ A i)
    (hregular : ∀ j : Fin n, X j.succ Q ∉ singularSupport A) :
    Q ∈ interior (backwardDomain f c u P) := by
  have hambient := mem_interior_backwardDomain_of_regular_limit f c v P W S C A wall
    hclosed hP hheight hdir hQ hendpoint hregular
  have hselected : ∀ᶠ Y in 𝓝 Q, ∀ j : Fin n,
      X j.succ Y ∈ A (wall j) → X j.succ Y ∈ P j := by
    apply eventually_all.mpr
    intro j
    exact (X j.succ).continuous.continuousAt.eventually
      (hlocal _ _ (backwardPoint_succ_mem_closure_of_mem_closure f c v P W S C hQ j)
        (hregular j))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [mem_interior_iff_mem_nhds.mp hambient, hselected] with Y hY hsel
  exact (mem_backwardDomain ..).mpr fun j =>
    ⟨((mem_backwardDomain ..).mp hY j).1, hsel j ((mem_backwardDomain ..).mp hY j).2⟩

end Support

/-- Every frontier point of the admissible domain is a boundary of the remaining
geometric constraints or a genuine singular contact of the extended negative
half-line. The singular cells need only be convex polyhedra; selected supports,
walls and the incoming source may be arbitrary sets. -/
theorem mem_frontier_admissibleBackwardDomain_imp_singular_or_mem_frontier [Finite K]
    (hS : ∀ a, TauCeti.IsConvexPolyhedron (S a)) {Q : V} (hQ : Q ∈ frontier D) :
    (∃ a s, s ≤ 0 ∧ backwardPath f c v Q s ∈ S a) ∨
      Q ∈ frontier ((backwardAvoidanceDomain f c u P W ∩
        backwardIncomingDomain f c u P (v (Fin.last n)) C W) ∩ {Q' | ∀ a, Q' ∉ W a}) := by
  by_cases hcontact : ∃ a s, s ≤ 0 ∧ backwardPath f c v Q s ∈ S a
  · exact Or.inl hcontact
  · right
    have hsub : D ⊆ (backwardAvoidanceDomain f c u P W ∩
        backwardIncomingDomain f c u P (v (Fin.last n)) C W) ∩ {Q' | ∀ a, Q' ∉ W a} := by
      intro Q' hQ'
      obtain ⟨hfinite, hincoming, _, hoff⟩ := (mem_admissibleBackwardDomain ..).mp hQ'
      exact ⟨⟨hfinite, hincoming⟩, hoff⟩
    refine ⟨closure_mono hsub (frontier_subset_closure hQ), fun hint => ?_⟩
    have havoid : ∀ a s, s ≤ 0 → backwardPath f c v Q s ∉ S a := by
      simpa only [not_exists, not_and] using hcontact
    have hnear := eventually_mem_backwardSingularAvoidanceDomain f c v P S hS
      (backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C
        (frontier_subset_closure hQ)) havoid
    apply hQ.2
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hnear, mem_interior_iff_mem_nhds.mp hint] with Q' hnear hother
    exact (mem_admissibleBackwardDomain ..).mpr ⟨hother.1.1, hother.1.2,
      hnear (backwardAvoidanceDomain_subset_backwardDomain f c u P W hother.1.1), hother.2⟩

/-- A regular limit with closed selected supports and a convex polyhedral source
is an admissible endpoint, provided recorded encounters preserve normal velocity.
Both kinds of singular avoidance concern the entire negative half-line. -/
theorem mem_admissibleBackwardDomain_of_regular_limit
    (hPclosed : ∀ j, IsClosed (P j)) (wall : Fin n → O)
    (hWclosed : ∀ a, IsClosed (W a)) (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (hnormal : ∀ j, f j (v j.succ) = f j (v j.castSucc))
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    (hC : TauCeti.IsConvexPolyhedron C)
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W)
    (havoid : ∀ a s, s ≤ 0 → backwardPath f c v Q s ∉ S a) : Q ∈ D := by
  have h0 := backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ
  have hτ (j : Fin (n + 1)) : τ j Q ≤ 0 := by
    simpa using antitone_backwardParameter f c u Q h0 (Fin.zero_le j)
  have hpos := backwardTime_pos_of_regular_limit f c v P W S C W wall hWclosed hP hheight
    hQ hoff fun j => by
      simpa only [backwardPath_apply_parameter f c v h0] using hregular (τ j.succ Q) (hτ _)
  have he : backwardPath f c v Q = (backwardRay f c v Q hpos).toContinuousMap := by
    rw [backwardPath_eq_backwardRay f c v Q hpos]
  apply (mem_admissibleBackwardDomain_iff f c v P W S C Q hpos).mpr
  refine ⟨?_, ?_, ?_, ?_, hoff⟩
  · intro j
    rw [backwardRay_apply_parameter]
    exact backwardPoint_succ_mem_of_mem_closure f c v P W S C hPclosed hQ j
  · simpa only [he, FiniteAffineRay.toContinuousMap_apply] using
      backwardPath_avoids_walls_of_regular_limit f c v P W S C wall hWclosed hP hheight
        hnormal ν z hspan hQ hoff hregular
  · simpa only [he, FiniteAffineRay.toContinuousMap_apply] using
      backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain f c v P W S C hC hQ
  · simpa only [he, FiniteAffineRay.toContinuousMap_apply] using havoid

/-- If a limit of admissible endpoints is not itself admissible, some wall
contains the endpoint or its negative half-line meets wall singular support or a
prescribed singular set. This classifies loss of admissibility, not every
domain frontier. -/
theorem notMem_admissibleBackwardDomain_imp_terminal_or_singular
    (hPclosed : ∀ j, IsClosed (P j)) (wall : Fin n → O)
    (hWclosed : ∀ a, IsClosed (W a)) (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (hnormal : ∀ j, f j (v j.succ) = f j (v j.castSucc))
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    (hC : TauCeti.IsConvexPolyhedron C)
    {Q : V} (hQ : Q ∈ closure D) (hnot : Q ∉ D) :
    (∃ a, Q ∈ W a) ∨ (∃ s ≤ 0, backwardPath f c v Q s ∈ singularSupport W) ∨
      ∃ a s, s ≤ 0 ∧ backwardPath f c v Q s ∈ S a := by
  by_contra hn
  push Not at hn
  exact hnot (mem_admissibleBackwardDomain_of_regular_limit f c v P W S C hPclosed wall
    hWclosed hP hheight hnormal ν z hspan hC hQ hn.1 hn.2.1 hn.2.2)

section Classification

variable [Finite O] [Finite K] (wall : Fin n → O)
  (hW : ∀ a, TauCeti.IsConvexPolyhedron (W a))
  (hP : ∀ j, P j ⊆ W (wall j))
  (hlocal : ∀ j x, x ∈ closure (P j) → x ∉ singularSupport W →
    ∀ᶠ y in 𝓝 x, y ∈ W (wall j) → y ∈ P j)
  (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (W (wall j))).direction)
  (hnormal : ∀ j, f j (v j.succ) = f j (v j.castSucc))
  (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
  (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
  (hS : ∀ a, TauCeti.IsConvexPolyhedron (S a))

local notation "Adm" =>
  Set.ofPred fun Q : V => ∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ C

include hW hP hlocal hheight hdir hnormal hspan hS

/-- At a regular limit, the admissible domain agrees locally with admission of
the incoming tail. The source may be any set; only walls and singular obstacles
need to be polyhedral. -/
theorem eventually_mem_admissibleBackwardDomain_iff_sourceAdmission_of_regular_limit
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W)
    (havoid : ∀ a s, s ≤ 0 → backwardPath f c v Q s ∉ S a) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D ↔ ∀ᶠ s : ℝ in atBot, backwardPath f c v Y s ∈ C := by
  have hclosed := fun a => (hW a).isClosed
  have h0 := backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ
  have hτ (j : Fin (n + 1)) : τ j Q ≤ 0 := by
    simpa only [backwardParameter_zero] using
      antitone_backwardParameter f c u Q h0 (Fin.zero_le j)
  have hinc := mem_interior_backwardDomain_of_regular_limit_of_eventually_mem
    f c v P W S C W wall hclosed hP hheight hdir hlocal hQ hoff fun j => by
      simpa only [backwardPath_apply_parameter f c v h0] using hregular (τ j.succ Q) (hτ _)
  have hsing := eventually_mem_backwardSingularAvoidanceDomain f c v P S hS h0 havoid
  have hnear := eventually_mem_admissibleBackwardDomain_iff_of_regular_limit f c v P W S C
    wall hW hP hheight hnormal ν z hspan hQ hoff hregular
  filter_upwards [hnear, hsing, mem_interior_iff_mem_nhds.mp hinc] with Y hnear hsing hinc
  rw [hnear, and_iff_right hinc, and_iff_left (hsing hinc), backwardPath_eventually_mem_iff]

/-- At a regular limit, belonging to the interior of the admissible domain is
equivalent to interior incoming-source admission. This includes unbounded
incoming tails and makes no openness assumption on the source. -/
theorem mem_interior_admissibleBackwardDomain_iff_sourceAdmission_of_regular_limit
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W)
    (havoid : ∀ a s, s ≤ 0 → backwardPath f c v Q s ∉ S a) :
    Q ∈ interior D ↔ Q ∈ interior Adm :=
  (eventually_mem_admissibleBackwardDomain_iff_sourceAdmission_of_regular_limit f c v P W S C
    wall hW hP hlocal hheight hdir hnormal ν z hspan hS hQ hoff hregular havoid).set_eq
    |>.mem_interior_iff

variable {ι : Type*} [Finite ι] (g : ι → V →ᴬ[ℝ] ℝ)

local notation "source" => Set.iInter fun j : ι => Set.ofPred fun x : V => g j x ≤ 0
local notation "Dg" => admissibleBackwardDomain f c v P W S source

/-- At a regular limit for a polyhedral source, the frontier of the admissible
domain is characterized exactly by a tight tangential source row whose pullback
along the incoming-base map is nonconstant. -/
theorem mem_frontier_admissibleBackwardDomain_iff_sourceFace_of_regular_limit
    {Q : V} (hQ : Q ∈ closure Dg) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W)
    (havoid : ∀ a s, s ≤ 0 → backwardPath f c v Q s ∉ S a) :
    Q ∈ frontier Dg ↔
      ∃ j, (g j).linear (v (Fin.last n)) = 0 ∧ g j (X (Fin.last n) Q) = 0 ∧
        ((g j).comp (X (Fin.last n))).toAffineMap.linear ≠ 0 := by
  have hsource : ∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ source := by
    apply backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain f c v P W S source
      _ hQ
    rw [iInter_ofPred]
    exact TauCeti.isConvexPolyhedron_setOf_forall g
  have hi := mem_interior_admissibleBackwardDomain_iff_sourceAdmission_of_regular_limit
    f c v P W S source wall hW hP hlocal hheight hdir hnormal ν z hspan hS hQ hoff hregular
    havoid
  have hf := mem_frontier_backwardPath_sourceAdmission_iff f c v g Q
  have hfront : Q ∈ frontier Dg ↔ Q ∉ interior Dg :=
    ⟨fun h => h.2, fun h => ⟨hQ, h⟩⟩
  have hsourcemem : Q ∈ {Y : V | ∀ᶠ s : ℝ in atBot, backwardPath f c v Y s ∈ source} :=
    hsource
  rw [hfront, hi, ← mem_frontier_iff_notMem_interior hsourcemem, hf, and_iff_right hsource]

/-- Every frontier point of the admissible domain has a terminal wall contact, a
wall-singular contact, a prescribed singular contact, or an incoming tail in a
tight tangential source face. Contact times are nonpositive and concern the
whole extended path. No boundary admissibility or codimension is asserted. -/
theorem mem_frontier_admissibleBackwardDomain_imp_terminal_or_singular_or_sourceFace
    {Q : V} (hQ : Q ∈ frontier Dg) :
    (∃ a, Q ∈ W a) ∨
      (∃ s ≤ 0, backwardPath f c v Q s ∈ singularSupport W) ∨
      (∃ a s, s ≤ 0 ∧ backwardPath f c v Q s ∈ S a) ∨
      ∃ j, (g j).linear (v (Fin.last n)) = 0 ∧
        ((g j).comp (X (Fin.last n))).toAffineMap.linear ≠ 0 ∧
        ∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ {x ∈ source | g j x = 0} := by
  by_cases ht : ∃ a, Q ∈ W a
  · exact Or.inl ht
  right
  by_cases hw : ∃ s ≤ 0, backwardPath f c v Q s ∈ singularSupport W
  · exact Or.inl hw
  right
  by_cases hs : ∃ a s, s ≤ 0 ∧ backwardPath f c v Q s ∈ S a
  · exact Or.inl hs
  right
  have hoff : ∀ a, Q ∉ W a := by simpa only [not_exists] using ht
  have hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W := by
    simpa only [not_exists, not_and] using hw
  have havoid : ∀ a s, s ≤ 0 → backwardPath f c v Q s ∉ S a := by
    simpa only [not_exists, not_and] using hs
  have hi := mem_interior_admissibleBackwardDomain_iff_sourceAdmission_of_regular_limit
    f c v P W S source wall hW hP hlocal hheight hdir hnormal ν z hspan hS
    (frontier_subset_closure hQ) hoff hregular havoid
  exact backwardPath_eventually_mem_sourceFace_of_mem_closure f c v g P W S
    (frontier_subset_closure hQ) (fun h => hQ.2 (hi.mpr h))

end Classification

end Mei.Convex
