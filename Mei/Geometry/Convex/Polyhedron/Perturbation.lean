/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Analysis.Convex.Intrinsic
public import Mei.Analysis.Normed.Affine.LineMap
public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Perturbing admissible segments and polygonal paths

Let `W` be a finite family of closed walls of codimension one in a finite-dimensional
real space. Admissibility of a segment between allowed points is stable under small
perturbations of its endpoints, and so are its crossings: every perturbed segment
crosses exactly the same walls, and two crossings occur in the same time order, or
simultaneously, before and after the perturbation. Simultaneous crossings occur only
on walls with a common supporting hyperplane, which a perturbed line still crosses at
a single parameter. Conversely, polygonal paths admissible for the whole family can be
found through vertices arbitrarily close to any prescribed list of vertices.

These are the two halves of moving a common admissible path of several wall families
into general position: small moves of the vertices keep the ordered crossings of every
family for which the path is admissible, and suitable small moves of the interior
vertices make it admissible for any further finite family of codimension-one polyhedra.

The crossing parameter of a perturbed line is the continuous function supplied by
`AffineSubspace.exists_continuousAt_lineMap_mem`; segments missing a closed set stay
away from it by the tube lemma `Mei.eventually_forall_lineMap_notMem`.
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : ι → Set V}

namespace WallComplement.AdmissibleSegment

variable {x y : WallComplement W}

/-- Segments close to an admissible segment stay transverse to every wall it meets. -/
private theorem eventually_sub_notMem_direction (e : AdmissibleSegment x y) {i : ι}
    (hi : ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x.val y.val t ∈ W i) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val), q.2 - q.1 ∉ (affineSpan ℝ (W i)).direction :=
  (continuous_snd.sub continuous_fst).continuousAt.eventually_mem
    ((Submodule.closed_of_finiteDimensional _).isOpen_compl.mem_nhds (e.transverse i hi))

/-- Near an admissible segment, the perturbed segments stay transverse to a wall it
crosses, and cross that wall exactly once, at a parameter depending continuously on the
endpoints. -/
private theorem exists_crossingTime
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (e : AdmissibleSegment x y) {i : ι} {t₀ : ℝ} (h : (i, t₀) ∈ crossings x y) :
    ∃ τ : V × V → ℝ, ContinuousAt τ (x.val, y.val) ∧ τ (x.val, y.val) = t₀ ∧
      ∀ᶠ q : V × V in 𝓝 (x.val, y.val), q.2 - q.1 ∉ (affineSpan ℝ (W i)).direction ∧
        ∀ s, (s ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap q.1 q.2 s ∈ W i) ↔ s = τ q := by
  obtain ⟨ht, hmem⟩ := (mem_crossings x y i t₀).mp h
  have htr := e.transverse i ⟨t₀, ht, hmem⟩
  obtain ⟨hIoo, hint⟩ := e.crossing_mem_intrinsicInterior ht hmem
  obtain ⟨τ, hτc, hτ, hτA⟩ := (affineSpan ℝ (W i)).exists_continuousAt_lineMap_mem (hdim i)
    htr (subset_affineSpan ℝ _ hmem)
  refine ⟨τ, hτc, hτ, ?_⟩
  have htrans := e.eventually_sub_notMem_direction ⟨t₀, ht, hmem⟩
  have hIoo' : ∀ᶠ q in 𝓝 (x.val, y.val), τ q ∈ Ioo (0 : ℝ) 1 :=
    hτc.eventually_mem (isOpen_Ioo.mem_nhds (hτ ▸ hIoo))
  have hpt : ContinuousAt (fun q : V × V => AffineMap.lineMap q.1 q.2 (τ q)) (x.val, y.val) :=
    continuousAt_fst.lineMap continuousAt_snd hτc
  have hlim : Tendsto (fun q : V × V => AffineMap.lineMap q.1 q.2 (τ q)) (𝓝 (x.val, y.val))
      (𝓝[affineSpan ℝ (W i)] AffineMap.lineMap x.val y.val t₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hτ] using hpt.tendsto, hτA⟩
  have hW := hlim.eventually_mem (mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hint)
  filter_upwards [htrans, hIoo', hW] with q hq hq₁ hq₂
  refine ⟨hq, fun s => ⟨fun hs => ?_, ?_⟩⟩
  · exact (affineSpan ℝ (W i)).subsingleton_preimage_lineMap (by simpa only [vsub_eq_sub] using hq)
      (subset_affineSpan ℝ _ hs.2) (subset_affineSpan ℝ _ hq₂)
  · rintro rfl
    exact ⟨Ioo_subset_Icc_self hq₁, hq₂⟩

omit [FiniteDimensional ℝ V] in
/-- Segments close to an admissible segment miss every wall it misses. -/
private theorem eventually_notMem_of_notMem (hclosed : ∀ i, IsClosed (W i)) {i : ι}
    (h : ∀ t, (i, t) ∉ crossings x y) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val), ∀ s ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap q.1 q.2 s ∉ W i :=
  eventually_forall_lineMap_notMem (hclosed i) fun t ht hti =>
    h t ((mem_crossings x y i t).mpr ⟨ht, hti⟩)

variable [Finite ι]

/-- Admissibility is stable: segments between allowed points close to the endpoints of
an admissible segment are admissible. -/
theorem eventually_admissibleSegment (hclosed : ∀ i, IsClosed (W i))
    (e : AdmissibleSegment x y) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val), ∀ x' y' : WallComplement W,
      x'.val = q.1 → y'.val = q.2 → AdmissibleSegment x' y' := by
  have htr (i : ι) : ∀ᶠ q : V × V in 𝓝 (x.val, y.val),
      (∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap q.1 q.2 t ∈ W i) →
        q.2 - q.1 ∉ (affineSpan ℝ (W i)).direction := by
    by_cases hi : ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x.val y.val t ∈ W i
    · filter_upwards [e.eventually_sub_notMem_direction hi] with q hq using fun _ => hq
    · filter_upwards [eventually_notMem_of_notMem hclosed fun t ht =>
          hi ⟨t, (mem_crossings x y i t).mp ht⟩] with q hq
      rintro ⟨t, ht, hti⟩
      exact absurd hti (hq t ht)
  have hreg := eventually_forall_lineMap_notMem (isClosed_singularSupport hclosed) e.regular
  filter_upwards [eventually_all.mpr htr, hreg] with ⟨a, b⟩ hq hq'
  rintro x' y' rfl rfl
  exact ⟨fun i hi => hq i hi, hq'⟩

/-- Crossed walls are stable: segments between allowed points close to the endpoints of
an admissible segment cross exactly the walls it crosses. -/
theorem eventually_exists_mem_crossings_iff (hclosed : ∀ i, IsClosed (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (e : AdmissibleSegment x y) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val), ∀ x' y' : WallComplement W,
      x'.val = q.1 → y'.val = q.2 →
        ∀ i, (∃ t, (i, t) ∈ crossings x' y') ↔ ∃ t, (i, t) ∈ crossings x y := by
  have hwall (i : ι) : ∀ᶠ q : V × V in 𝓝 (x.val, y.val),
      (∃ s, s ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap q.1 q.2 s ∈ W i) ↔
        ∃ t, (i, t) ∈ crossings x y := by
    by_cases hi : ∃ t, (i, t) ∈ crossings x y
    · obtain ⟨t, hit⟩ := hi
      obtain ⟨τ, -, -, hτ⟩ := e.exists_crossingTime hdim hit
      filter_upwards [hτ] with q hq
      exact iff_of_true ⟨τ q, (hq.2 _).mpr rfl⟩ ⟨t, hit⟩
    · filter_upwards [eventually_notMem_of_notMem hclosed (not_exists.mp hi)] with q hq
      exact iff_of_false (fun ⟨s, hs, hsi⟩ => hq s hs hsi) hi
  filter_upwards [eventually_all.mpr hwall] with ⟨a, b⟩ hq
  rintro x' y' rfl rfl i
  simp only [mem_crossings] at hq ⊢
  exact hq i

/-- Crossing order is stable: for segments between allowed points close to the endpoints
of an admissible segment, two walls are crossed in the same strict time order as along
the original segment. In particular simultaneous crossings remain simultaneous. -/
theorem eventually_lt_iff_of_mem_crossings
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (e : AdmissibleSegment x y) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val), ∀ x' y' : WallComplement W,
      x'.val = q.1 → y'.val = q.2 → ∀ {i j : ι} {s t s' t' : ℝ},
        (i, s) ∈ crossings x y → (j, t) ∈ crossings x y →
          (i, s') ∈ crossings x' y' → (j, t') ∈ crossings x' y' → (s' < t' ↔ s < t) := by
  have hpair (i j : ι) : ∀ᶠ q : V × V in 𝓝 (x.val, y.val), ∀ {s t s' t' : ℝ},
      (i, s) ∈ crossings x y → (j, t) ∈ crossings x y →
        (s' ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap q.1 q.2 s' ∈ W i) →
          (t' ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap q.1 q.2 t' ∈ W j) → (s' < t' ↔ s < t) := by
    by_cases hij : (∃ s, (i, s) ∈ crossings x y) ∧ ∃ t, (j, t) ∈ crossings x y
    · obtain ⟨⟨s₀, hs₀⟩, ⟨t₀, ht₀⟩⟩ := hij
      obtain ⟨σ, hσc, hσ, hσq⟩ := e.exists_crossingTime hdim hs₀
      obtain ⟨τ, hτc, hτ, hτq⟩ := e.exists_crossingTime hdim ht₀
      -- The perturbed crossing parameters compare as the original ones.
      have horder : ∀ᶠ q : V × V in 𝓝 (x.val, y.val), (σ q < τ q ↔ s₀ < t₀) := by
        rcases lt_trichotomy s₀ t₀ with hlt | heq | hgt
        · filter_upwards [hσc.eventually_lt hτc (by rwa [hσ, hτ])] with q hq
          exact iff_of_true hq hlt
        · -- Simultaneous crossings lie on walls with a common supporting hyperplane.
          subst heq
          obtain ⟨hs, hsi⟩ := (mem_crossings x y i s₀).mp hs₀
          have hsj := ((mem_crossings x y j s₀).mp ht₀).2
          have hdir : (affineSpan ℝ (W i)).direction = (affineSpan ℝ (W j)).direction := by
            by_contra hne
            exact e.regular s₀ hs (mem_singularSupport.mpr (Or.inr ⟨i, j, hne, hsi, hsj⟩))
          have hspan : affineSpan ℝ (W i) = affineSpan ℝ (W j) :=
            AffineSubspace.ext_of_direction_eq hdir
              ⟨_, subset_affineSpan ℝ _ hsi, subset_affineSpan ℝ _ hsj⟩
          filter_upwards [hσq, hτq] with q hqi hqj
          have hσi := ((hqi.2 (σ q)).mpr rfl).2
          have hτj := ((hqj.2 (τ q)).mpr rfl).2
          have he : σ q = τ q := (affineSpan ℝ (W j)).subsingleton_preimage_lineMap
            (by simpa only [vsub_eq_sub] using hqj.1)
            (hspan ▸ subset_affineSpan ℝ _ hσi) (subset_affineSpan ℝ _ hτj)
          exact iff_of_false (fun h => h.ne he) (lt_irrefl _)
        · filter_upwards [hτc.eventually_lt hσc (by rwa [hσ, hτ])] with q hq
          exact iff_of_false hq.asymm hgt.asymm
      filter_upwards [hσq, hτq, horder] with q hqi hqj hq
      intro s t s' t' hs ht hs' ht'
      obtain rfl := e.subsingleton_crossing i ((mem_crossings x y i s).mp hs)
        ((mem_crossings x y i s₀).mp hs₀)
      obtain rfl := e.subsingleton_crossing j ((mem_crossings x y j t).mp ht)
        ((mem_crossings x y j t₀).mp ht₀)
      rwa [(hqi.2 s').mp hs', (hqj.2 t').mp ht']
    · exact Eventually.of_forall fun q s t s' t' hs ht => absurd ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ hij
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr (hpair i)] with ⟨a, b⟩ hq
  rintro x' y' rfl rfl i j s t s' t' hs ht hs' ht'
  exact hq i j hs ht ((mem_crossings x' y' i s').mp hs') ((mem_crossings x' y' j t').mp ht')

end WallComplement.AdmissibleSegment

namespace AdmissiblePLPath

/-- In a finite family of codimension-one polyhedra, any nonempty list `l` of interior
vertices is approximated, within any positive distance, by the interior vertices of an
admissible polygonal path between two allowed points. -/
theorem exists_forall₂_dist_lt [Finite ι] (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    {l : List V} (hl : l ≠ []) {ε : ℝ} (hε : 0 < ε) (x y : WallComplement W) :
    ∃ p : AdmissiblePLPath x y, List.Forall₂ (fun a b => dist a b < ε)
      (x.val :: (l ++ [y.val])) (p.vertices.map WallComplement.val) := by
  induction l generalizing x with
  | nil => exact absurd rfl hl
  | cons v l ih =>
    by_cases hl' : l = []
    · subst hl'
      obtain ⟨u, hu, hz, htrans, hreg⟩ := exists_mem_open_two_transverse_lineMaps
        W hpoly hdim x.notMem y.notMem Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
      let z : WallComplement W := ⟨u, hz⟩
      have hxz : WallComplement.AdmissibleSegment x z :=
        ⟨fun i _ => (htrans i).1, fun t _ => (hreg t).1⟩
      have hyz : WallComplement.AdmissibleSegment y z :=
        ⟨fun i _ => (htrans i).2, fun t _ => (hreg t).2⟩
      refine ⟨((Quiver.Path.nil : AdmissiblePLPath x x).cons (PLift.up hxz)).cons
        (PLift.up hyz.symm), ?_⟩
      simp only [Quiver.Path.vertices_cons, Quiver.Path.vertices_nil, List.concat_eq_append,
        List.nil_append, List.cons_append, List.map_cons, List.map_nil]
      exact .cons (by simpa using hε) (.cons (Metric.mem_ball'.mp hu)
        (.cons (by simpa using hε) .nil))
    · obtain ⟨u, hu, hz, htrans, hreg⟩ := exists_mem_open_two_transverse_lineMaps
        W hpoly hdim x.notMem x.notMem Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
      let z : WallComplement W := ⟨u, hz⟩
      have hxz : WallComplement.AdmissibleSegment x z :=
        ⟨fun i _ => (htrans i).1, fun t _ => (hreg t).1⟩
      obtain ⟨q, hq⟩ := ih hl' z
      refine ⟨(Quiver.Hom.toPath (PLift.up hxz)).comp q, ?_⟩
      obtain ⟨T, hT⟩ : ∃ T, q.vertices.map WallComplement.val = u :: T := by
        rcases hv : q.vertices with _ | ⟨a, T⟩
        · exact absurd hv q.vertices_ne_nil
        · have ha := q.vertices_head?
          rw [hv, List.head?_cons, Option.some.injEq] at ha
          exact ⟨T.map WallComplement.val, by rw [List.map_cons, ha]⟩
      rw [hT] at hq
      have hcomp : ((Quiver.Hom.toPath (PLift.up hxz)).comp q).vertices.map WallComplement.val =
          x.val :: u :: T := by
        rw [Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath, List.dropLast_cons_cons,
          List.dropLast_singleton, List.singleton_append, List.map_cons, hT]
      rw [hcomp, List.cons_append]
      exact .cons (by simpa using hε) (.cons (Metric.mem_ball'.mp hu) (List.forall₂_cons.mp hq).2)

end AdmissiblePLPath

end Mei.Convex
