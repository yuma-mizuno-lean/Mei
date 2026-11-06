/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Avoidance
public import Mei.Geometry.Convex.Sweep.Contact.Stability

/-!
# Relative stability of wall avoidance in complete decorated types

Near a regular limiting ray with endpoint off the walls, absence of unrecorded
wall encounters persists relative to the selected incidence domain. This includes
the entire incoming half-line, tangent walls, and unchanged-degree encounters.
The selected event supports may be nonclosed subsets of closed ambient walls.

Consequently wall avoidance introduces no independent boundary event at such a
limit: the remaining constraints are selected incidences, incoming-source
admission and singular avoidance. No assertion of full admissibility of boundary
paths is made. Complete coefficient histories and incoming tails are retained.
The closed-family interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite O]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)
  (t : CutoffDecoratedType d ℳ T a v f ε k)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "w" => fun j : Fin t.itinerary.val.length => u (Fin.castSucc j)
local notation "A" => fun j => P (t.itinerary.val.get j)
local notation "X" => backwardPoint F b w
local notation "τ" => backwardParameter F b w
local notation "D" => backwardDomain F b w A

/-- At a regular limit with allowed endpoint, wall avoidance persists relative
to the selected support and positive-time constraints. Both finite open segments
and the open incoming ray are included; source admission remains separate. -/
theorem eventually_avoids_walls_of_regular
    (wall : J → O) (hW : ∀ a, TauCeti.IsConvexPolyhedron (W a))
    (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    {Q : V} (hQ : Q ∈ closure (domain c P W S C t))
    (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W) :
    ∀ᶠ Q' in 𝓝 Q, Q' ∈ D →
      Q' ∈ backwardAvoidanceDomain F b w A W ∧
        ∀ a (s : ℝ), 0 < s → X (Fin.last t.itinerary.val.length) Q' +
          s • u (Fin.last t.itinerary.val.length) ∉ W a := by
  have hclosed := fun a => (hW a).isClosed
  have h0 := t.backwardTime_nonneg c P W S C hQ
  have hτ (j : Fin (t.itinerary.val.length + 1)) : τ j Q ≤ 0 := by
    simpa only [backwardParameter_zero] using
      antitone_backwardParameter F b w Q h0 (Fin.zero_le j)
  have hpos := t.backwardTime_pos_of_notMem_singularSupport c P W S C W wall
    hclosed hP hheight hQ hoff (fun j => by
      simpa only [Fin.snoc_castSucc] using hregular (τ j.succ Q) (hτ _))
  have hout (j : Fin t.itinerary.val.length) : F j (u j.castSucc) ≠ 0 := by
    intro hz
    have hp := hpos j
    simp only [Fin.snoc_castSucc] at hz
    simp only [backwardTime_apply, Fin.snoc_castSucc, hz, div_zero, lt_self_iff_false] at hp
  have hin (j : Fin t.itinerary.val.length) : F j (u j.succ) ≠ 0 := by
    have hn := ((mem_decoratedHistorySupport ℳ (fun j => T (t.itinerary.val.get j))
      0 a v F (fun j => ε (t.itinerary.val.get j)) t.history.val).mp t.history.property).2 j |>.1
    simpa only [Fin.snoc_castSucc, hn] using hout j
  have hinc (j : Fin t.itinerary.val.length) : X j.succ Q ∈ W (wall (t.itinerary.val.get j)) :=
    closure_minimal (s := domain c P W S C t)
      (t := (X j.succ) ⁻¹' W (wall (t.itinerary.val.get j)))
      (fun Y hY => hP _ (((mem_backwardDomain ..).mp
        (admissibleBackwardDomain_subset_backwardDomain _ _ _ _ _ _ _
          ((t.mem_domain c P W S C Y).mp hY)) j).2))
      ((hclosed _).preimage (X j.succ).continuous) hQ
  -- At a regular recorded contact all incident hyperplanes agree. Thus incidence
  -- fixes every relevant height, and transversality transfers to every normal.
  have hcontact (j : Fin t.itinerary.val.length) (a : O) (q : V)
      (hq : F j q ≠ 0) (ha : X j.succ Q ∈ W a) :
      ν a q ≠ 0 ∧ ∀ Y ∈ D, ν a (X j.succ Y) = z a := by
    have hreg : X j.succ Q ∉ singularSupport W := by
      simpa only [path_def, backwardPath_apply_parameter F b u h0] using
        hregular (τ j.succ Q) (hτ _)
    have heq := affineSpan_eq_of_notMem_singularSupport hreg ha (hinc j)
    constructor
    · intro hz
      have hx : X j.succ Q + q ∈ affineSpan ℝ (W (wall (t.itinerary.val.get j))) := by
        rw [← heq]
        apply (hspan a).symm.subset
        simpa only [mem_ofPred_eq, map_add, hz, add_zero] using
          (hspan a).subset (subset_affineSpan ℝ _ ha)
      have hh := AffineMap.eqOn_affineSpan
        (f := (F j).toLinearMap.toAffineMap) (g := AffineMap.const ℝ V (b j))
        (hheight (t.itinerary.val.get j)) hx
      apply hq
      simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe,
        AffineMap.const_apply, map_add, hheight _ _ (hinc j), add_eq_left] using hh
    · intro Y hY
      apply (hspan a).subset
      rw [heq]
      exact subset_affineSpan ℝ _ (hP _ (((mem_backwardDomain ..).mp hY j).2))
  have havoid := (backwardRay_avoids_iff F b u Q hpos W).mp fun a s hs hne => by
    simpa only [path_def, backwardPath_eq_backwardRay F b u Q hpos,
      FiniteAffineRay.toContinuousMap_apply] using
      t.path_avoids_walls_of_regular c P W S C wall hclosed hP hheight ν z hspan
        hQ hoff hregular a s hs hne
  -- The regular limiting ray avoids each open piece. Pinning boundary contacts
  -- lets the finite-segment stability theorem retain precisely these exclusions.
  have hfinite : ∀ᶠ Y in 𝓝 Q, ∀ (j : Fin t.itinerary.val.length) a,
      Y ∈ D → ∀ s : ℝ, 0 < s → s < backwardTime F b w j Y →
        X j.castSucc Y + s • u j.castSucc ∉ W a := by
    refine eventually_all.mpr fun j => eventually_all.mpr fun a => ?_
    apply (ν a).eventually_forall_notMem_of_openSegment (hclosed a)
      (fun x hx => (hspan a).subset (subset_affineSpan ℝ _ hx))
      (X j.castSucc).continuous.continuousAt (backwardTime F b w j).continuous.continuousAt
      (hpos j)
    · exact fun s hs hs' => havoid.1 j a s hs hs'
    · intro ha
      rcases Fin.eq_zero_or_eq_succ j.castSucc with hj | ⟨e, he⟩
      · exact (hoff a (by simpa only [hj, backwardPoint_zero,
          ContinuousAffineMap.coe_id, id_eq] using ha)).elim
      · rw [he] at ha ⊢
        exact hcontact e a _ (hin e) ha
    · intro ha
      rw [← backwardPoint_succ_apply] at ha
      have hh := hcontact j a _ (hout j) ha
      simpa only [backwardPoint_succ_apply] using hh
  -- The incoming half-line uses the closed polyhedral sweep, so no new contact
  -- can arrive from infinity as the endpoint varies.
  have htail : ∀ᶠ Y in 𝓝 Q, ∀ a, Y ∈ D → ∀ s : ℝ, 0 < s →
      X (Fin.last t.itinerary.val.length) Y + s • u (Fin.last t.itinerary.val.length) ∉ W a := by
    refine eventually_all.mpr fun a => ?_
    apply (ν a).eventually_forall_notMem_of_openRay (hW a)
      (fun x hx => (hspan a).subset (subset_affineSpan ℝ _ hx))
      (X (Fin.last t.itinerary.val.length)).continuous.continuousAt
    · exact fun s hs => havoid.2 a s hs
    · intro ha
      rcases Fin.eq_zero_or_eq_succ (Fin.last t.itinerary.val.length) with hj | ⟨e, he⟩
      · exact (hoff a (by simpa only [hj, backwardPoint_zero,
          ContinuousAffineMap.coe_id, id_eq] using ha)).elim
      · rw [he] at ha ⊢
        exact hcontact e a _ (hin e) ha
  filter_upwards [hfinite, htail] with Y hfinite htail hY
  exact ⟨(mem_backwardAvoidanceDomain ..).mpr ⟨hY, fun j a s hs hs' =>
    hfinite j a hY s hs hs'⟩, fun a s hs => htail a hY s hs⟩

/-- Near a regular limiting ray, complete admissibility consists precisely of
selected incidence, incoming-source admission and singular avoidance. Allowedness
and absence of unrecorded wall encounters impose no further local constraint. -/
theorem eventually_mem_domain_iff_of_regular
    (wall : J → O) (hW : ∀ a, TauCeti.IsConvexPolyhedron (W a))
    (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    {Q : V} (hQ : Q ∈ closure (domain c P W S C t))
    (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ domain c P W S C t ↔
      Y ∈ D ∧
        (∀ᶠ s : ℝ in atTop, X (Fin.last t.itinerary.val.length) Y +
          s • u (Fin.last t.itinerary.val.length) ∈ C) ∧
        Y ∈ backwardSingularAvoidanceDomain F b u A S := by
  have hnear := t.eventually_avoids_walls_of_regular c P W S C wall hW hP hheight ν z hspan
    hQ hoff hregular
  have hallowed : ∀ᶠ Y in 𝓝 Q, ∀ a, Y ∉ W a :=
    eventually_all.mpr fun a => (hW a).isClosed.isOpen_compl.mem_nhds (hoff a)
  filter_upwards [hnear, hallowed] with Y hnear hallowed
  constructor
  · intro hY
    obtain ⟨hfinite, hincoming, hsing, _⟩ :=
      (mem_admissibleBackwardDomain ..).mp ((t.mem_domain c P W S C Y).mp hY)
    exact ⟨backwardAvoidanceDomain_subset_backwardDomain _ _ _ _ _ hfinite,
      ((mem_backwardIncomingDomain ..).mp hincoming).2.2, hsing⟩
  · rintro ⟨hD, hsource, hsing⟩
    obtain ⟨hfinite, htail⟩ := hnear hD
    exact (t.mem_domain c P W S C Y).mpr ((mem_admissibleBackwardDomain ..).mpr
      ⟨hfinite, (mem_backwardIncomingDomain ..).mpr ⟨hD, htail, hsource⟩, hsing, hallowed⟩)

end Mei.CutoffDecoratedType
