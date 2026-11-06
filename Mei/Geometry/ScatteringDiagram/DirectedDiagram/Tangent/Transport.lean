/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Tangent

/-!
# Shrinking tangent paths into a directed diagram

Every finite polygonal path admissible for the incident tangent diagram can be shrunk
about its base point into the original diagram. At a fixed cutoff, sufficiently small
positive homotheties preserve admissibility and the entire ordered wall product.
The shrinking factor may depend on the path and cutoff. Walls missing the base point
are excluded locally; coincident incident walls retain all their factors.

This uses the local support, singular-support and combined-label comparisons in
`DirectedDiagram.Tangent`. It supplies the path comparison used to pass consistency to
incident tangent diagrams. For the scattering-diagram conventions, see Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, §2.1.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι) {x : V}

/-- Positive scaling of a regular tangent point leaves its combined crossing label unchanged. -/
@[simp↓]
theorem combinedLabel_tangentAt_smul (k : ℕ) (v w : V) {r : ℝ} (hr : 0 < r)
    (hrv : r • v ∉ singularSupport (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)) :
    (D.tangentAt x).combinedLabel k (r • v) w hrv =
      (D.tangentAt x).combinedLabel k v w
        (fun hm => hrv ((D.smul_mem_singularSupport_tangentAt_iff k hr v).mpr hm)) := by
  classical
  have hv : v ∉ singularSupport (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support) :=
    fun hm => hrv ((D.smul_mem_singularSupport_tangentAt_iff k hr v).mpr hm)
  let l := (Set.toFinite {j : (D.tangentAt x).active k |
    v ∈ ((D.tangentAt x).wall j).support}).toFinset.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hm : ∀ j, j ∈ l ↔ v ∈ ((D.tangentAt x).wall j).support := by simp [l]
  rw [(D.tangentAt x).combinedLabel_eq_prod k _ _ hrv l hl (fun j =>
    (hm j).trans (by
      simpa only [tangentAt_wall] using
        ((D.wall j.1.1).smul_mem_tangentAt_support_iff j.1.2 hr v).symm)),
    (D.tangentAt x).combinedLabel_eq_prod k _ _ hv l hl hm]

/-- On any bounded collection of displacements, sufficiently small homotheties identify
all active wall incidences with the corresponding incident tangent walls. -/
theorem eventually_forall_mem_support_add_smul_iff (k : ℕ) {K : Set V}
    (hK : Bornology.IsBounded K) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ v ∈ K, ∀ j : D.active k,
      x + r • v ∈ (D.wall j).support ↔
        ∃ hj : x ∈ (D.wall j).support, v ∈ ((D.wall j).tangentAt x hj).support := by
  have huniform := eventually_singleton_add_smul_subset (𝕜 := ℝ) hK
    (D.eventually_forall_mem_support_iff (x := x) k)
  filter_upwards [huniform.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hrpos
  intro v hv j
  have hc := hr (Set.add_mem_add (Set.mem_singleton x) (Set.smul_mem_smul_set hv)) j
  simp only [add_sub_cancel_left] at hc
  exact hc.trans (exists_congr fun hj =>
    (D.wall j.1).smul_mem_tangentAt_support_iff hj hrpos v)

/-- On bounded displacements, every regular tangent germ has the original combined label
at all sufficiently small positive scales, for every crossing direction. -/
theorem eventually_forall_combinedLabel_add_smul (k : ℕ) {K : Set V}
    (hK : Bornology.IsBounded K) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ v ∈ K,
      ∀ (hv : v ∉ singularSupport (fun j : (D.tangentAt x).active k =>
        ((D.tangentAt x).wall j).support)),
      ∃ hv' : x + r • v ∉ singularSupport (fun j : D.active k => (D.wall j).support),
        ∀ w : V, D.combinedLabel k (x + r • v) w hv' =
          (D.tangentAt x).combinedLabel k v w hv := by
  have huniform := eventually_singleton_add_smul_subset (𝕜 := ℝ) hK
    (D.eventually_combinedLabel_tangentAt (x := x) k)
  filter_upwards [huniform.filter_mono nhdsWithin_le_nhds,
    D.eventually_forall_mem_singularSupport_add_smul_iff (x := x) k hK,
    self_mem_nhdsWithin] with r hr hs hrpos
  intro v hv hreg
  have hreg' := fun hm => hreg ((hs v hv).mp hm)
  obtain ⟨hscaled, heq⟩ := hr
    (Set.add_mem_add (Set.mem_singleton x) (Set.smul_mem_smul_set hv)) hreg'
  refine ⟨hreg', fun w => ?_⟩
  have he := heq w
  simp only [add_sub_cancel_left] at he
  have hscaled' : r • v ∉ singularSupport (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support) := by
    simpa only [add_sub_cancel_left] using hscaled
  exact he.trans (D.combinedLabel_tangentAt_smul k v w hrpos hscaled')

/-- An admissible segment of the tangent diagram shrinks to an admissible segment of the
original diagram, preserving its signed, ordered product at the chosen cutoff. -/
theorem eventually_exists_tangentAt_segment (k : ℕ)
    {u v : WallComplement (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)} (e : u ⟶ v) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∃ (u' v' : WallComplement (fun j : D.active k => (D.wall j).support)) (e' : u' ⟶ v'),
        u'.val = x + r • u.val ∧ v'.val = x + r • v.val ∧
          D.levelPathProduct k e'.toPath = (D.tangentAt x).levelPathProduct k e.toPath := by
  -- First choose one scale controlling every point of the compact segment.
  let K := AffineMap.lineMap u.val v.val '' Icc (0 : ℝ) 1
  have hK : Bornology.IsBounded K :=
    (isCompact_Icc.image AffineMap.lineMap_continuous).isBounded
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap u.val v.val t ∈ K := ⟨t, ht, rfl⟩
  filter_upwards [D.eventually_forall_mem_support_add_smul_iff (x := x) k hK,
    D.eventually_forall_combinedLabel_add_smul (x := x) k hK,
    self_mem_nhdsWithin] with r hsupport hlabel hr
  have hoff (z : WallComplement (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)) (hz : z.val ∈ K) :
      ∀ j : D.active k, x + r • z.val ∉ (D.wall j).support := by
    intro j hm
    obtain ⟨hj, hm⟩ := (hsupport z.val hz j).mp hm
    apply z.notMem ⟨⟨j.1, hj⟩, (D.mem_active_tangentAt x k _).mpr j.2⟩
    simpa only [tangentAt_wall] using hm
  -- Reconstruct the scaled endpoints and verify transversality and regularity.
  let u' : WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨x + r • u.val, hoff u (by simpa using hmem 0 ⟨le_rfl, zero_le_one⟩)⟩
  let v' : WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨x + r • v.val, hoff v (by simpa using hmem 1 ⟨zero_le_one, le_rfl⟩)⟩
  have hline (t : ℝ) : AffineMap.lineMap u'.val v'.val t =
      x + r • AffineMap.lineMap u.val v.val t := by
    simp only [u', v', AffineMap.lineMap_apply_module]
    module
  have hsub : v'.val - u'.val = r • (v.val - u.val) := by
    simp only [u', v']
    module
  have hregular (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap u'.val v'.val t ∉
        singularSupport (fun j : D.active k => (D.wall j).support) := by
    rw [hline]
    exact (hlabel _ (hmem t ht) (e.down.regular t ht)).choose
  let e' : u' ⟶ v' := ⟨{
    transverse j hj := by
      obtain ⟨t, ht, hm⟩ := hj
      rw [hline] at hm
      obtain ⟨hjx, hm⟩ := (hsupport _ (hmem t ht) j).mp hm
      let j' : (D.tangentAt x).active k :=
        ⟨⟨j.1, hjx⟩, (D.mem_active_tangentAt x k _).mpr j.2⟩
      have hm' : AffineMap.lineMap u.val v.val t ∈
          ((D.tangentAt x).wall j').support := by
        simpa only [j', tangentAt_wall] using hm
      have htrans := e.down.transverse j' ⟨t, ht, hm'⟩
      simp only [j', tangentAt_wall, DirectedWall.tangentAt_support,
        (D.wall j).isConvexPolyhedron.direction_affineSpan_posTangentConeAt hjx] at htrans
      rw [hsub]
      exact fun hm => htrans (((affineSpan ℝ (D.wall j).support).direction).smul_mem_iff
        hr.ne' |>.mp hm)
    regular := hregular }⟩
  refine ⟨u', v', e', rfl, rfl, ?_⟩
  -- Compare simultaneous products at each parameter, then assemble them in time order.
  rw [D.levelPathProduct_eq_wallPathProduct k _ (D.activeLabels_commute k),
    (D.tangentAt x).levelPathProduct_eq_wallPathProduct k _
      ((D.tangentAt x).activeLabels_commute k),
    Quiver.Path.wallPathProduct_toPath, Quiver.Path.wallPathProduct_toPath]
  apply segmentPathProduct_eq_of_crossingEventProduct_eq
  intro t ht
  obtain ⟨hreg, heq⟩ := hlabel _ (hmem t ht) (e.down.regular t ht)
  have hcombined : D.combinedLabel k (AffineMap.lineMap u'.val v'.val t)
      (v'.val - u'.val) (e'.down.regular t ht) =
      (D.tangentAt x).combinedLabel k (AffineMap.lineMap u.val v.val t)
        (v.val - u.val) (e.down.regular t ht) := by
    simpa only [hline, hsub, D.combinedLabel_smul_pos k _ _ hreg hr] using
      heq (v.val - u.val)
  have hevent := (D.crossingEventProduct_eq_combinedLabel k e' ht).trans
    (hcombined.trans ((D.tangentAt x).crossingEventProduct_eq_combinedLabel k e ht).symm)
  -- Event products use the categorical tower carrier, while combined labels use BCH groups.
  convert hevent using 1 <;> rfl

/-- Every finite tangent path is realized in the original diagram at every sufficiently
small positive scale, with precisely its scaled vertices and the same ordered product. -/
theorem eventually_exists_tangentAt_path (k : ℕ)
    {u v : WallComplement (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)} (p : AdmissiblePLPath u v) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∃ (u' v' : WallComplement (fun j : D.active k => (D.wall j).support))
        (q : AdmissiblePLPath u' v'),
        u'.val = x + r • u.val ∧ v'.val = x + r • v.val ∧
          q.vertices.map WallComplement.val = p.vertices.map (fun z => x + r • z.val) ∧
          D.levelPathProduct k q = (D.tangentAt x).levelPathProduct k p := by
  induction p with
  | nil =>
    filter_upwards [D.eventually_forall_mem_support_add_smul_iff (x := x) k
      (Bornology.isBounded_singleton (x := u.val))] with r hr
    have hoff : ∀ j : D.active k, x + r • u.val ∉ (D.wall j).support := by
      intro j hm
      obtain ⟨hj, hm⟩ := (hr u.val (mem_singleton _) j).mp hm
      apply u.notMem ⟨⟨j.1, hj⟩, (D.mem_active_tangentAt x k _).mpr j.2⟩
      simpa only [tangentAt_wall] using hm
    let u' : WallComplement (fun j : D.active k => (D.wall j).support) := ⟨_, hoff⟩
    exact ⟨u', u', .nil, rfl, rfl, by simp [u'], by simp⟩
  | @cons v w p e ih =>
    filter_upwards [ih, D.eventually_exists_tangentAt_segment k e] with r hp he
    obtain ⟨u', v', q, hu, hv, hvertices, hprod⟩ := hp
    obtain ⟨v'', w', e', hv'', hw, heprod⟩ := he
    have hvv : v'' = v' := WallComplement.ext (hv''.trans hv.symm)
    subst v''
    refine ⟨u', w', q.cons e', hu, hw, ?_, ?_⟩
    · simp only [Quiver.Path.vertices_cons, List.map_concat, hvertices, hw]
    · rw [D.levelPathProduct_cons, hprod, heprod,
        (D.tangentAt x).levelPathProduct_cons]

end Mei.DirectedDiagram
