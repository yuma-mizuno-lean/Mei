/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Avoidance
public import Mei.Geometry.Convex.Sweep.Admissible.Limit
public import Mei.Geometry.Convex.Sweep.Collision
public import Mei.Geometry.Convex.Sweep.Contact.Stability

/-!
# Regular limits of admissible backward paths

Consider a limit of endpoints of admissible backward rays with fixed directions,
selected supports and incoming source. Suppose its endpoint misses the closed
ambient walls and its whole negative half-line misses their singular support.
Then no encounter interval collapses, and no unrecorded wall encounter appears,
provided every recorded encounter preserves normal velocity. This includes
tangential contacts on every finite segment and on the incoming half-line.

For convex polyhedral walls these exclusions persist on a neighborhood of the
limiting endpoint. Near such a regular limit, full admissibility therefore
reduces to selected incidence with positive times, admission of the incoming
tail to its source, and avoidance of the prescribed singular sets.

The statements concern the backward path family itself, so they apply to every
broken-line carrier whose type paths are backward paths. Normal-velocity
preservation is a hypothesis: for decorated rays it is part of the surviving
history condition. The closed-family interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
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
local notation "B" => backwardDomain f c (fun j : Fin n => v (Fin.castSucc j)) P

/-- Enlarging the selected supports keeps every admissible endpoint in the
corresponding strict incidence domain. -/
theorem admissibleBackwardDomain_subset_backwardDomain_of_subset {A : Fin n → Set V}
    (hPA : ∀ j, P j ⊆ A j) : D ⊆ backwardDomain f c u A := fun Q hQ =>
  (mem_backwardDomain f c u A Q).mpr fun j =>
    have h := (mem_backwardDomain f c u P Q).mp
      (admissibleBackwardDomain_subset_backwardDomain f c v P W S C hQ) j
    ⟨h.1, hPA j h.2⟩

/-- A limiting endpoint off the ambient walls, with every recorded encounter
outside their singular support, has no collapsed encounter intervals. -/
theorem backwardTime_pos_of_regular_limit {ι : Type*} (A : ι → Set V) (wall : Fin n → ι)
    (hclosed : ∀ i, IsClosed (A i)) (hP : ∀ j, P j ⊆ A (wall j))
    (hheight : ∀ j x, x ∈ A (wall j) → f j x = c j)
    {Q : V} (hQ : Q ∈ closure D) (hendpoint : ∀ i, Q ∉ A i)
    (hregular : ∀ j : Fin n, X j.succ Q ∉ singularSupport A) (j : Fin n) :
    0 < backwardTime f c u j Q := by
  rcases eq_or_lt_of_le
    (backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ j)
    with hz | hpos
  · rcases backwardTime_eq_zero_imp_terminal_or_singularSupport f c u A wall hheight hclosed
      (admissibleBackwardDomain_subset_backwardDomain_of_subset f c v P W S C hP) hQ j hz.symm
      with ⟨_, hwall⟩ | hsing
    · exact (hendpoint _ hwall).elim
    · exact (hregular j hsing).elim
  · exact hpos

/-- A regular limit whose recorded encounters preserve normal velocity has no
unrecorded wall encounters, on finite segments or on the incoming half-line.
Tangential contacts and zero spatial directions are included. -/
theorem backwardPath_avoids_walls_of_regular_limit
    (wall : Fin n → O) (hclosed : ∀ a, IsClosed (W a))
    (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (hnormal : ∀ j, f j (v j.succ) = f j (v j.castSucc))
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W) :
    ∀ a s, s < 0 → (∀ j : Fin n, s ≠ τ j.succ Q) → backwardPath f c v Q s ∉ W a := by
  have h0 := backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ
  have hτ (j : Fin (n + 1)) : τ j Q ≤ 0 := by
    simpa using antitone_backwardParameter f c u Q h0 (Fin.zero_le j)
  have hpos := backwardTime_pos_of_regular_limit f c v P W S C W wall hclosed hP hheight
    hQ hoff fun j => by
      simpa only [backwardPath_apply_parameter f c v h0] using hregular (τ j.succ Q) (hτ _)
  have htrans (j : Fin n) : f j (v j.succ) ≠ 0 := by
    intro hz
    have hp := hpos j
    simp only [backwardTime_apply, ← hnormal j, hz, div_zero, lt_self_iff_false] at hp
  have havoid := backwardPath_notMem_wall_of_regular_limit f c v P W S C wall hclosed hP
    hheight htrans ν z hspan hQ hoff hregular
  rw [backwardPath_eq_backwardRay f c v Q hpos]
  simp only [FiniteAffineRay.toContinuousMap_apply]
  apply (backwardRay_avoids_iff f c v Q hpos W).mpr
  constructor
  · intro j a s hs hs'
    have ha := havoid j.castSucc hs (fun e he => by
      have he' : j = e := Fin.castSucc_injective _ he
      simpa only [← he'] using hs') a
    rwa [backwardPath_apply_segment f c v h0 j hs.le hs'.le] at ha
  · intro a s hs
    have ha := havoid (Fin.last _) hs (fun e he => (Fin.castSucc_ne_last e he.symm).elim) a
    rwa [backwardPath_apply_incoming f c v h0 hs.le] at ha

variable [Finite O]

/-- At a regular limit with allowed endpoint and convex polyhedral walls, wall
avoidance persists relative to the selected support and positive-time constraints.
Both finite open segments and the open incoming ray are included; source admission
remains separate. -/
theorem eventually_avoids_walls_of_regular_limit
    (wall : Fin n → O) (hW : ∀ a, TauCeti.IsConvexPolyhedron (W a))
    (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (hnormal : ∀ j, f j (v j.succ) = f j (v j.castSucc))
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W) :
    ∀ᶠ Q' in 𝓝 Q, Q' ∈ B →
      Q' ∈ backwardAvoidanceDomain f c u P W ∧
        ∀ a (s : ℝ), 0 < s → X (Fin.last n) Q' + s • v (Fin.last n) ∉ W a := by
  have hclosed := fun a => (hW a).isClosed
  have h0 := backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ
  have hτ (j : Fin (n + 1)) : τ j Q ≤ 0 := by
    simpa only [backwardParameter_zero] using
      antitone_backwardParameter f c u Q h0 (Fin.zero_le j)
  have hpos := backwardTime_pos_of_regular_limit f c v P W S C W wall hclosed hP hheight
    hQ hoff fun j => by
      simpa only [backwardPath_apply_parameter f c v h0] using hregular (τ j.succ Q) (hτ _)
  have hout (j : Fin n) : f j (v j.castSucc) ≠ 0 := by
    intro hz
    have hp := hpos j
    simp only [backwardTime_apply, hz, div_zero, lt_self_iff_false] at hp
  have hin (j : Fin n) : f j (v j.succ) ≠ 0 := by
    simpa only [hnormal j] using hout j
  have hinc (j : Fin n) : X j.succ Q ∈ W (wall j) :=
    closure_minimal (s := D) (t := (X j.succ) ⁻¹' W (wall j))
      (fun Y hY => hP _ (((mem_backwardDomain ..).mp
        (admissibleBackwardDomain_subset_backwardDomain _ _ _ _ _ _ _ hY)) j).2)
      ((hclosed _).preimage (X j.succ).continuous) hQ
  -- At a regular recorded contact all incident hyperplanes agree. Thus incidence
  -- fixes every relevant height, and transversality transfers to every normal.
  have hcontact (j : Fin n) (a : O) (q : V) (hq : f j q ≠ 0) (ha : X j.succ Q ∈ W a) :
      ν a q ≠ 0 ∧ ∀ Y ∈ B, ν a (X j.succ Y) = z a := by
    have hreg : X j.succ Q ∉ singularSupport W := by
      simpa only [backwardPath_apply_parameter f c v h0] using hregular (τ j.succ Q) (hτ _)
    have heq := affineSpan_eq_of_notMem_singularSupport hreg ha (hinc j)
    constructor
    · intro hz
      exact hq ((f j).toLinearMap.map_eq_zero_of_affineSpan_eq (ν a).toLinearMap
        (hheight _) (hspan a) heq.symm (hinc j) hz)
    · intro Y hY
      apply (hspan a).subset
      rw [heq]
      exact subset_affineSpan ℝ _ (hP _ (((mem_backwardDomain ..).mp hY j).2))
  -- Every contact of a base point with a wall is a recorded one, since the
  -- initial point is off all walls.
  have hbase (j : Fin (n + 1)) (a : O) (ha : X j Q ∈ W a) :
      ν a (v j) ≠ 0 ∧ ∀ Y ∈ B, ν a (X j Y) = z a := by
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨e, he⟩
    · exact (hoff a (by simpa only [hj, backwardPoint_zero,
        ContinuousAffineMap.coe_id, id_eq] using ha)).elim
    · rw [he] at ha ⊢
      exact hcontact e a _ (hin e) ha
  have havoid := (backwardRay_avoids_iff f c v Q hpos W).mp fun a s hs hne => by
    simpa only [backwardPath_eq_backwardRay f c v Q hpos,
      FiniteAffineRay.toContinuousMap_apply] using
      backwardPath_avoids_walls_of_regular_limit f c v P W S C wall hclosed hP hheight
        hnormal ν z hspan hQ hoff hregular a s hs hne
  -- The regular limiting ray avoids each open piece. Pinning boundary contacts
  -- lets the finite-segment stability theorem retain precisely these exclusions.
  have hfinite : ∀ᶠ Y in 𝓝 Q, ∀ (j : Fin n) a,
      Y ∈ B → ∀ s : ℝ, 0 < s → s < backwardTime f c u j Y →
        X j.castSucc Y + s • v j.castSucc ∉ W a := by
    refine eventually_all.mpr fun j => eventually_all.mpr fun a => ?_
    apply (ν a).eventually_forall_notMem_of_openSegment (hclosed a)
      (fun x hx => (hspan a).subset (subset_affineSpan ℝ _ hx))
      (X j.castSucc).continuous.continuousAt (backwardTime f c u j).continuous.continuousAt
    · exact fun s hs hs' => havoid.1 j a s hs hs'
    · exact hbase j.castSucc a
    · intro ha
      rw [← backwardPoint_succ_apply] at ha
      have hh := hcontact j a _ (hout j) ha
      simpa only [backwardPoint_succ_apply] using hh
  -- The incoming half-line uses the closed polyhedral sweep, so no new contact
  -- can arrive from infinity as the endpoint varies.
  have htail : ∀ᶠ Y in 𝓝 Q, ∀ a, Y ∈ B → ∀ s : ℝ, 0 < s →
      X (Fin.last n) Y + s • v (Fin.last n) ∉ W a := by
    refine eventually_all.mpr fun a => ?_
    apply (ν a).eventually_forall_notMem_of_openRay (hW a)
      (fun x hx => (hspan a).subset (subset_affineSpan ℝ _ hx))
      (X (Fin.last n)).continuous.continuousAt
    · exact fun s hs => havoid.2 a s hs
    · exact hbase _ a
  filter_upwards [hfinite, htail] with Y hfinite htail hY
  exact ⟨(mem_backwardAvoidanceDomain ..).mpr ⟨hY, fun j a s hs hs' =>
    hfinite j a hY s hs hs'⟩, fun a s hs => htail a hY s hs⟩

/-- Near a regular limit, full admissibility consists precisely of selected
incidence with positive times, incoming-source admission and singular avoidance.
Allowedness and absence of unrecorded wall encounters impose no further local
constraint. -/
theorem eventually_mem_admissibleBackwardDomain_iff_of_regular_limit
    (wall : Fin n → O) (hW : ∀ a, TauCeti.IsConvexPolyhedron (W a))
    (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (hnormal : ∀ j, f j (v j.succ) = f j (v j.castSucc))
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, backwardPath f c v Q s ∉ singularSupport W) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D ↔
      Y ∈ B ∧ (∀ᶠ s : ℝ in atTop, X (Fin.last n) Y + s • v (Fin.last n) ∈ C) ∧
        Y ∈ backwardSingularAvoidanceDomain f c v P S := by
  have hnear := eventually_avoids_walls_of_regular_limit f c v P W S C wall hW hP hheight
    hnormal ν z hspan hQ hoff hregular
  have hallowed : ∀ᶠ Y in 𝓝 Q, ∀ a, Y ∉ W a :=
    eventually_all.mpr fun a => (hW a).isClosed.isOpen_compl.mem_nhds (hoff a)
  filter_upwards [hnear, hallowed] with Y hnear hallowed
  constructor
  · intro hY
    obtain ⟨hfinite, hincoming, hsing, _⟩ := (mem_admissibleBackwardDomain ..).mp hY
    exact ⟨backwardAvoidanceDomain_subset_backwardDomain _ _ _ _ _ hfinite,
      ((mem_backwardIncomingDomain ..).mp hincoming).2.2, hsing⟩
  · rintro ⟨hD, hsource, hsing⟩
    obtain ⟨hfinite, htail⟩ := hnear hD
    exact (mem_admissibleBackwardDomain ..).mpr
      ⟨hfinite, (mem_backwardIncomingDomain ..).mpr ⟨hD, htail, hsource⟩, hsing, hallowed⟩

end Mei.Convex
