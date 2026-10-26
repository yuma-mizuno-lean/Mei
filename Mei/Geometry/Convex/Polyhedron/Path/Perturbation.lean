/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.CrossingEvents
public import Mei.Geometry.Convex.Polyhedron.Perturbation

/-!
# Signed events of perturbed wall-family paths

The ordered list of simultaneous signed crossing events is locally constant in
the vertices of an admissible polygonal path through a finite family of closed
codimension-one walls. Endpoints may move, and coincident indexed walls remain
grouped together. This permits perturbing paths into general position for further
wall families without changing the original signed crossing data.

The geometric input is `AdmissibleSegment.eventually_exists_mem_crossings_iff`
and `AdmissibleSegment.eventually_lt_iff_of_mem_crossings`. We match distinct
crossing times, rather than ordering individual walls, so the argument also
handles simultaneous crossings. The normal-sign and vertex-radius arguments adapt
Claude's crossing-word construction in
`Mei.Geometry.Convex.PolyhedralComplex.Perturbation`.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι] {W : ι → Set V}
  {x y : WallComplement W}

/-- Close admissible segments retain all simultaneous signed events, in the same
order, even when several indexed walls have the same supporting hyperplane. -/
theorem eventually_segmentCrossingEvents_eq
    (hclosed : ∀ i, IsClosed (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 =
      Module.finrank ℝ V)
    (ν : ι → V →ₗ[ℝ] ℝ)
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val),
      ∀ (x' y' : WallComplement W) (e' : x' ⟶ y'),
        x'.val = q.1 → y'.val = q.2 →
          segmentCrossingEvents ν e' = segmentCrossingEvents ν e := by
  classical
  have hsign (i : ι) : ∀ᶠ q : V × V in 𝓝 (x.val, y.val),
      (∃ t, (i, t) ∈ crossings x y) →
        (0 < ν i (q.2 - q.1) ↔ 0 < ν i (y.val - x.val)) := by
    by_cases hi : ∃ t, (i, t) ∈ crossings x y
    · obtain ⟨t, ht⟩ := hi
      have hne : ν i (y.val - x.val) ≠ 0 := by
        rw [Ne, ← LinearMap.mem_ker, hν]
        exact e.down.transverse i ⟨t, (mem_crossings x y i t).mp ht⟩
      have hc : ContinuousAt (fun q : V × V => ν i (q.2 - q.1)) (x.val, y.val) :=
        ((ν i).continuous_of_finiteDimensional.comp
          (continuous_snd.sub continuous_fst)).continuousAt
      rcases hne.lt_or_gt with hlt | hgt
      · filter_upwards [hc.eventually_lt continuousAt_const hlt] with q hq
        exact fun _ => iff_of_false hq.asymm hlt.asymm
      · filter_upwards [continuousAt_const.eventually_lt hc hgt] with q hq
        exact fun _ => iff_of_true hq hgt
    · exact Eventually.of_forall fun _ h => absurd h hi
  filter_upwards [e.down.eventually_exists_mem_crossings_iff hclosed hdim,
    e.down.eventually_lt_iff_of_mem_crossings hdim, eventually_all.mpr hsign]
    with ⟨a, b⟩ hwalls horder hsign
  rintro x' y' e' rfl rfl
  have hwalls := hwalls x' y' rfl rfl
  have hlt : ∀ {i j : ι} {s t s' t' : ℝ},
      (i, s) ∈ crossings x y → (j, t) ∈ crossings x y →
      (i, s') ∈ crossings x' y' → (j, t') ∈ crossings x' y' → (s' < t' ↔ s < t) :=
    horder x' y' rfl rfl
  -- Equality of crossing times is preserved as well as strict order.
  have heq {i j : ι} {s t s' t' : ℝ}
      (hs : (i, s) ∈ crossings x y) (ht : (j, t) ∈ crossings x y)
      (hs' : (i, s') ∈ crossings x' y') (ht' : (j, t') ∈ crossings x' y') :
      s' = t' ↔ s = t :=
    eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt (hlt hs ht hs' ht') (hlt ht hs ht' hs')
  -- Pick a new time for each old event, using any incident wall.
  have htime : ∀ t ∈ orderedCrossingTimes e, ∃ t',
      (∃ i, (i, t') ∈ crossings x' y') ∧
      ∀ i, (i, t') ∈ crossings x' y' ↔ (i, t) ∈ crossings x y := by
    intro t ht
    obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes e t).mp ht
    obtain ⟨t', hi'⟩ := (hwalls i).mpr ⟨t, hi⟩
    refine ⟨t', ⟨i, hi'⟩, fun j => ⟨?_, ?_⟩⟩
    · intro hj'
      obtain ⟨s, hs⟩ := (hwalls j).mp ⟨t', hj'⟩
      exact (heq hs hi hj' hi').mp rfl ▸ hs
    · intro hj
      obtain ⟨s', hs'⟩ := (hwalls j).mpr ⟨t, hj⟩
      exact (heq hj hi hs' hi').mpr rfl ▸ hs'
  choose τ hτmem hτ using htime
  let f : ℝ → ℝ := fun t => if ht : t ∈ orderedCrossingTimes e then τ t ht else 0
  have hf (t : ℝ) (ht : t ∈ orderedCrossingTimes e) : f t = τ t ht := dite_eq_left ht
  have hsorted : ((orderedCrossingTimes e).map f).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    refine (pairwise_orderedCrossingTimes e).imp_of_mem fun hs ht hst => ?_
    obtain ⟨i, hi'⟩ := hτmem _ hs
    obtain ⟨j, hj'⟩ := hτmem _ ht
    rw [hf _ hs, hf _ ht]
    exact (hlt ((hτ _ hs i).mp hi') ((hτ _ ht j).mp hj') hi' hj').mpr hst
  have htimes : orderedCrossingTimes e' = (orderedCrossingTimes e).map f := by
    apply (pairwise_orderedCrossingTimes e').eq_of_mem_iff hsorted
    intro t'
    rw [mem_orderedCrossingTimes]
    simp only [List.mem_map]
    constructor
    · rintro ⟨i, hi'⟩
      obtain ⟨t, hi⟩ := (hwalls i).mp ⟨t', hi'⟩
      have ht := (mem_orderedCrossingTimes e t).mpr ⟨i, hi⟩
      refine ⟨t, ht, ?_⟩
      rw [hf _ ht]
      exact e'.down.subsingleton_crossing i
        ((mem_crossings x' y' i _).mp ((hτ _ ht i).mpr hi))
        ((mem_crossings x' y' i _).mp hi')
    · rintro ⟨t, ht, rfl⟩
      rw [hf _ ht]
      exact hτmem _ ht
  simp only [segmentCrossingEvents_def, htimes, List.map_map]
  apply List.map_congr_left
  intro t ht
  rw [Function.comp_apply, hf _ ht]
  ext ⟨i, s⟩
  simp only [mem_signedCrossingEvent, hτ]
  exact and_congr_right fun hi => by simp only [hsign i ⟨t, hi⟩]

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι] {W : ι → Set V}
  {x y : WallComplement W}

/-- An admissible polygonal path has a positive vertex-perturbation radius within
which every admissible path retains its ordered simultaneous signed events.
The endpoints may move along with the interior vertices. -/
theorem exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt
    (hclosed : ∀ i, IsClosed (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 =
      Module.finrank ℝ V)
    (ν : ι → V →ₗ[ℝ] ℝ)
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (p : AdmissiblePLPath x y) :
    ∃ ε > 0, ∀ {x' y' : WallComplement W} (q : AdmissiblePLPath x' y'),
      List.Forall₂ (fun a b => dist a b < ε) (p.vertices.map WallComplement.val)
        (q.vertices.map WallComplement.val) →
          q.signedCrossingEvents ν = p.signedCrossingEvents ν := by
  have hsplit {S : V → V → Prop} {l₁ l₂ : List V} {a b : V} :
      List.Forall₂ S (l₁ ++ [a]) (l₂ ++ [b]) → List.Forall₂ S l₁ l₂ ∧ S a b := by
    rw [← List.forall₂_reverse_iff]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.forall₂_cons, List.forall₂_reverse_iff]
    exact And.symm
  induction p with
  | nil =>
    refine ⟨1, one_pos, fun {x' y'} q hq => ?_⟩
    cases q with
    | nil => simp
    | cons q e =>
      have := hq.length_eq
      simp at this
  | @cons z w p e ih =>
    obtain ⟨ε₁, hε₁, hp⟩ := ih
    obtain ⟨ε₂, hε₂, he⟩ := Metric.eventually_nhds_iff.mp
      (eventually_segmentCrossingEvents_eq hclosed hdim ν hν e)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun {x' y'} q hq => ?_⟩
    cases q with
    | nil =>
      have := hq.length_eq
      simp at this
    | @cons z' w' q e' =>
      simp only [vertices_cons, List.concat_eq_append, List.map_append, List.map_cons,
        List.map_nil] at hq
      obtain ⟨hq, hw⟩ := hsplit hq
      have hz : dist z.val z'.val < min ε₁ ε₂ := by
        have hq' := hq
        rw [← p.dropLast_append_end_eq, ← q.dropLast_append_end_eq, List.map_append,
          List.map_append, List.map_singleton, List.map_singleton] at hq'
        exact (hsplit hq').2
      rw [signedCrossingEvents_cons, signedCrossingEvents_cons,
        hp q (hq.imp fun _ _ hab => hab.trans_le (min_le_left _ _))]
      congr 1
      refine he (y := (z'.val, _)) ?_ z' _ e' rfl rfl
      rw [Prod.dist_eq, max_lt_iff, dist_comm z'.val, dist_comm _ w.val]
      exact ⟨hz.trans_le (min_le_right _ _), hw.trans_le (min_le_right _ _)⟩

end Quiver.Path

namespace Mei.Convex.CommonWallComplement

variable {V J K : Type*} {I : J → Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Countable J] [∀ j, Finite (I j)] [Finite K]
  {W : ∀ j, I j → Set V}

/-- Approximate a shared vertex list by a path admissible for countably many
finite wall families, fixing its endpoints and retaining the complete signed
event lists in finitely many selected families. At least one interior vertex is
required; coincident and overlapping walls within each family are allowed. -/
theorem exists_forall₂_dist_lt_signedCrossingEvents_eq
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (W j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 =
      Module.finrank ℝ V)
    (a : K → J) (ν : ∀ k, I (a k) → V →ₗ[ℝ] ℝ)
    (hν : ∀ k i, LinearMap.ker (ν k i) = (affineSpan ℝ (W (a k) i)).direction)
    {x y : CommonWallComplement W} {l : List V} (hl : l ≠ [])
    {ε : ℝ} (hε : 0 < ε)
    (p : ∀ k, AdmissiblePLPath (projection (a k) x) (projection (a k) y))
    (hp : ∀ k, (p k).vertices.map WallComplement.val = x.val :: (l ++ [y.val])) :
    ∃ q : Quiver.Path x y,
      List.Forall₂ (fun u v => dist u v < ε) (x.val :: (l ++ [y.val]))
        (q.vertices.map CommonWallComplement.val) ∧
      ∀ k, ((projectionPrefunctor (a k)).mapPath q).signedCrossingEvents (ν k) =
        (p k).signedCrossingEvents (ν k) := by
  classical
  let := Fintype.ofFinite K
  choose r hr hevents using fun k =>
    (p k).exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt
      (fun i => (hpoly (a k) i).isClosed) (hdim (a k)) (ν k) (hν k)
  -- Include the requested radius to handle even an empty collection of tests.
  let radius : Option K → ℝ := fun k => k.elim ε r
  let δ := Finset.univ.inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (Option K)).Nonempty) radius
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff _).mpr
    intro k _
    cases k with
    | none => exact hε
    | some k => exact hr k
  have hδε : δ ≤ ε := Finset.inf'_le radius (Finset.mem_univ (none : Option K))
  obtain ⟨q, hq⟩ := exists_forall₂_dist_lt hpoly hdim hl hδ x y
  refine ⟨q, hq.imp (fun _ _ huv => huv.trans_le hδε), fun k => ?_⟩
  apply hevents k
  rw [hp k, vertices_projection (a k) q]
  exact hq.imp (fun _ _ huv => huv.trans_le
    (Finset.inf'_le radius (Finset.mem_univ (some k))))

end Mei.Convex.CommonWallComplement
