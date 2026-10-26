/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mei.Analysis.Convex.Intrinsic
public import Mei.Analysis.Normed.Affine.LineMap
public import Mei.Geometry.Affine.Segment
public import Mei.Geometry.Convex.Polyhedron.CommonPath

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

Normal signs are stable as well. The shared theorem
`Quiver.Path.exists_pos_invariant_eq_of_forall₂_dist_lt` lifts stability of segment
data to stability of recursively accumulated path invariants.
`CommonWallComplement.exists_forall₂_dist_lt_forall` retains finitely many locally
constant tests while choosing a common admissible path. The normal-sign and
path-invariant arguments are extracted from Claude's crossing-word stability proof
in `Mei.Geometry.Convex.PolyhedralComplex.Perturbation`.

The crossing parameter of a perturbed line is the continuous function supplied by
`AffineSubspace.exists_continuousAt_lineMap_mem`; segments missing a closed set stay
away from it by `IsClosed.isOpen_setOf_lineMap_notMem`.
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
  ((hclosed i).isOpen_setOf_lineMap_notMem).mem_nhds fun t ht hti =>
    h t ((mem_crossings x y i t).mpr ⟨ht, hti⟩)

/-- The normal velocity at a crossed wall keeps its sign when the segment's
endpoints move sufficiently little. No closedness or codimension assumption is needed. -/
theorem eventually_pos_iff_of_mem_crossings (e : AdmissibleSegment x y)
    (i : ι) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (W i)).direction) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val),
      (∃ t, (i, t) ∈ crossings x y) →
        (0 < ν (q.2 - q.1) ↔ 0 < ν (y.val - x.val)) := by
  by_cases hi : ∃ t, (i, t) ∈ crossings x y
  · obtain ⟨t, ht⟩ := hi
    have hne : ν (y.val - x.val) ≠ 0 := by
      rw [Ne, ← LinearMap.mem_ker, hν]
      exact e.transverse i ⟨t, (mem_crossings x y i t).mp ht⟩
    have hc : ContinuousAt (fun q : V × V => ν (q.2 - q.1)) (x.val, y.val) :=
      (ν.continuous_of_finiteDimensional.comp
        (continuous_snd.sub continuous_fst)).continuousAt
    rcases hne.lt_or_gt with hlt | hgt
    · filter_upwards [hc.eventually_lt continuousAt_const hlt] with q hq
      exact fun _ => iff_of_false hq.asymm hlt.asymm
    · filter_upwards [continuousAt_const.eventually_lt hc hgt] with q hq
      exact fun _ => iff_of_true hq hgt
  · exact Eventually.of_forall fun _ h => absurd h hi

variable [Finite ι]

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
  let x' : CommonWallComplement (fun _ : Unit => W) := ⟨x.val, fun _ => x.notMem⟩
  let y' : CommonWallComplement (fun _ : Unit => W) := ⟨y.val, fun _ => y.notMem⟩
  obtain ⟨p, hp⟩ := CommonWallComplement.exists_forall₂_dist_lt
    (fun _ => hpoly) (fun _ => hdim) hl hε x' y'
  have hp' : ∃ q : Quiver.Path
      ((CommonWallComplement.projectionPrefunctor ()).obj x')
      ((CommonWallComplement.projectionPrefunctor ()).obj y'),
      List.Forall₂ (fun a b => dist a b < ε) (x.val :: (l ++ [y.val]))
        (q.vertices.map WallComplement.val) := by
    refine ⟨(CommonWallComplement.projectionPrefunctor ()).mapPath p, ?_⟩
    exact (CommonWallComplement.vertices_projection () p).symm ▸ hp
  have hx : (CommonWallComplement.projectionPrefunctor ()).obj x' = x := by
    ext
    simp [x']
  have hy : (CommonWallComplement.projectionPrefunctor ()).obj y' = y := by
    ext
    simp [y']
  rw [hx, hy] at hp'
  exact hp'

/-- A closed vertex list can be approximated by an admissible loop, with its
basepoint also allowed to move, even when there are no interior vertices. -/
theorem exists_loop_forall₂_dist_lt [Finite ι]
    (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (v : V) {l : List V} {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : WallComplement W) (p : AdmissiblePLPath x x),
      List.Forall₂ (fun a b => dist a b < ε) (v :: (l ++ [v]))
        (p.vertices.map WallComplement.val) := by
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨u, hu, hW⟩ := AffineSubspace.exists_dist_lt_genericLocus
    (fun i => affineSpan ℝ (W i))
    (fun i => (affineSpan ℝ (W i)).ne_top_of_finrank_direction_add_one_eq (hdim i)) v hhalf
  let x : WallComplement W := ⟨u, fun i hi => hW i (subset_affineSpan ℝ _ hi)⟩
  have hv : dist v x.val < ε / 2 := by simpa only [dist_comm] using hu
  by_cases hl : l = []
  · subst l
    have he : WallComplement.AdmissibleSegment x x := by
      refine WallComplement.AdmissibleSegment.refl x (fun hs => ?_)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
        (singularSupport_subset_iUnion W (fun i => (hpoly i).isClosed) hs)
      exact x.notMem i hi
    refine ⟨x, Quiver.Hom.toPath (PLift.up he), ?_⟩
    have hv' : dist v x.val < ε := hv.trans (half_lt_self hε)
    simp only [Quiver.Path.vertices_toPath, List.nil_append, List.map_cons, List.map_nil]
    exact .cons hv' (.cons hv' .nil)
  obtain ⟨p, hp⟩ := exists_forall₂_dist_lt hpoly hdim hl hhalf x x
  have hs : List.Forall₂ (fun a b => dist a b < ε / 2)
      (v :: (l ++ [v])) (x.val :: (l ++ [x.val])) :=
    .cons hv (List.rel_append (List.forall₂_same.mpr fun _ _ => by simpa using hhalf)
      (.cons hv .nil))
  refine ⟨x, p, List.forall₂_of_length_eq_of_get (hs.length_eq.trans hp.length_eq) ?_⟩
  intro j hj₁ hj₃
  have hj₂ : j < (x.val :: (l ++ [x.val])).length := by simpa using hj₁
  exact (dist_triangle _ ((x.val :: (l ++ [x.val])).get ⟨j, hj₂⟩) _).trans_lt
    (by linarith [hs.get hj₁ hj₂, hp.get hj₂ hj₃])

end AdmissiblePLPath

namespace CommonWallComplement

variable {J K : Type*} {I : J → Type*}
  [Countable J] [∀ j, Finite (I j)] [Finite K] {W : ∀ j, I j → Set V}

/-- Approximate a vertex list by a common admissible path while satisfying finitely
many tests, each of which holds for all sufficiently close projected paths. -/
theorem exists_forall₂_dist_lt_forall
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (W j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 =
      Module.finrank ℝ V)
    (a : K → J) {x y : CommonWallComplement W} {l : List V} (hl : l ≠ [])
    {ε : ℝ} (hε : 0 < ε)
    (test : ∀ k, AdmissiblePLPath (projection (a k) x) (projection (a k) y) → Prop)
    (htest : ∀ k, ∃ r > 0,
      ∀ q : AdmissiblePLPath (projection (a k) x) (projection (a k) y),
        List.Forall₂ (fun u v => dist u v < r) (x.val :: (l ++ [y.val]))
          (q.vertices.map WallComplement.val) → test k q) :
    ∃ q : Quiver.Path x y,
      List.Forall₂ (fun u v => dist u v < ε) (x.val :: (l ++ [y.val]))
        (q.vertices.map CommonWallComplement.val) ∧
      ∀ k, test k ((projectionPrefunctor (a k)).mapPath q) := by
  classical
  let := Fintype.ofFinite K
  choose r hr htest using htest
  -- The extra index also handles an empty collection of tests.
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
  apply htest k
  exact (vertices_projection (a k) q).symm ▸
    hq.imp (fun _ _ huv => huv.trans_le
      (Finset.inf'_le radius (Finset.mem_univ (some k))))

end CommonWallComplement

end Mei.Convex

namespace Quiver.Path

open Mei.Convex Mei.Convex.WallComplement

variable {V ι A B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y : WallComplement W}

/-- A recursively accumulated path invariant is stable under small vertex movements
if its segment data are stable under small endpoint movements. The accumulation
operation need not satisfy any algebraic laws. -/
theorem exists_pos_invariant_eq_of_forall₂_dist_lt (p : AdmissiblePLPath x y)
    (segment : {u v : WallComplement W} → (u ⟶ v) → A)
    (invariant : {u v : WallComplement W} → AdmissiblePLPath u v → B)
    (initial : B) (append : B → A → B)
    (hnil : ∀ u, invariant (Quiver.Path.nil : AdmissiblePLPath u u) = initial)
    (hcons : ∀ {u v w : WallComplement W} (p : AdmissiblePLPath u v) (e : v ⟶ w),
      invariant (p.cons e) = append (invariant p) (segment e))
    (hsegment : ∀ {u v : WallComplement W} (e : u ⟶ v),
      ∀ᶠ q : V × V in 𝓝 (u.val, v.val),
        ∀ (u' v' : WallComplement W) (e' : u' ⟶ v'),
          u'.val = q.1 → v'.val = q.2 → segment e' = segment e) :
    ∃ ε > 0, ∀ {x' y' : WallComplement W} (q : AdmissiblePLPath x' y'),
      List.Forall₂ (fun a b => dist a b < ε) (p.vertices.map WallComplement.val)
        (q.vertices.map WallComplement.val) → invariant q = invariant p := by
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
    | nil => rw [hnil, hnil]
    | cons q e =>
      have := hq.length_eq
      simp at this
  | @cons z w p e ih =>
    obtain ⟨ε₁, hε₁, hp⟩ := ih
    obtain ⟨ε₂, hε₂, he⟩ := Metric.eventually_nhds_iff.mp (hsegment e)
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
      rw [hcons, hcons,
        hp q (hq.imp fun _ _ hab => hab.trans_le (min_le_left _ _))]
      congr 1
      refine he (y := (z'.val, _)) ?_ z' _ e' rfl rfl
      rw [Prod.dist_eq, max_lt_iff, dist_comm z'.val, dist_comm _ w.val]
      exact ⟨hz.trans_le (min_le_right _ _), hw.trans_le (min_le_right _ _)⟩

end Quiver.Path
