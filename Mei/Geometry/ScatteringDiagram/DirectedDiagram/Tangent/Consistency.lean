/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Tangent

/-!
# Consistency of incident tangent diagrams

Every admissible polygonal path in a tangent diagram can be shrunk toward the base
point to an admissible path in the original diagram with the same finite-order product.
The shrinking factor may depend on the path and cutoff. Thus consistency passes to the
tangent diagram, including at singular points and for supports which are not full
hyperplanes. This allows local scattering constructions to use the incident cones.

The comparison uses the local support and singular-support identifications of
`DirectedDiagram.tangentAt`, uniformly on each compact segment, and the simultaneous
crossing-product comparison. It retains separate indices for coincident walls.
For the application to local broken-line wall crossing, see Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5).
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

/-- Every tangent segment has, at all sufficiently small positive scales, an original
admissible segment with the same product and the prescribed dilated endpoints. -/
theorem eventually_exists_segment_levelPathProduct_tangentAt (k : ℕ)
    {a b : WallComplement (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)} (e : a ⟶ b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∃ (a' b' : WallComplement (fun j : D.active k => (D.wall j).support)) (e' : a' ⟶ b'),
        a'.val = x + t • a.val ∧ b'.val = x + t • b.val ∧
          D.levelPathProduct k e'.toPath = (D.tangentAt x).levelPathProduct k e.toPath := by
  -- Shrink the whole segment into the neighbourhood where both local comparisons hold.
  have hK : Bornology.IsBounded (segment ℝ a.val b.val) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image
      (AffineMap.lineMap_continuous (R := ℝ) (p := a.val) (q := b.val))).isBounded
  have huniform := eventually_singleton_add_smul_subset (𝕜 := ℝ) hK
    (D.eventually_combinedLabel_tangentAt (x := x) k)
  filter_upwards [D.eventually_forall_mem_support_add_smul_iff (x := x) k hK,
    D.eventually_forall_mem_singularSupport_add_smul_iff (x := x) k hK,
    huniform.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hS hsing hlabel ht
  -- Off-wall endpoints remain off-wall, and transversality survives positive scaling.
  have hoff (v : WallComplement (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)) (hv : v.val ∈ segment ℝ a.val b.val) :
      ∀ j : D.active k, x + t • v.val ∉ (D.wall j).support := by
    intro j hj
    obtain ⟨hxj, hjv⟩ := (hS v.val hv j).mp hj
    exact v.notMem ⟨⟨j.1, hxj⟩, (D.mem_active_tangentAt x k _).mpr j.2⟩
      (by simpa only [tangentAt_wall] using hjv)
  let a' : WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨x + t • a.val, hoff a (left_mem_segment ℝ _ _)⟩
  let b' : WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨x + t • b.val, hoff b (right_mem_segment ℝ _ _)⟩
  have hline (s : ℝ) : AffineMap.lineMap a'.val b'.val s =
      x + t • AffineMap.lineMap a.val b.val s := by
    simp only [a', b', AffineMap.lineMap_apply_module]
    module
  have hsub : b'.val - a'.val = t • (b.val - a.val) := by
    dsimp only [a', b']
    module
  have hmem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap a.val b.val s ∈ segment ℝ a.val b.val :=
    lineMap_mem_segment ℝ a.val b.val hs
  let e' : a' ⟶ b' := ⟨{
    transverse := by
      rintro j ⟨s, hs, hj⟩ hd
      rw [hline] at hj
      obtain ⟨hxj, hjv⟩ := (hS _ (hmem hs) j).mp hj
      let j' : (D.tangentAt x).active k :=
        ⟨⟨j.1, hxj⟩, (D.mem_active_tangentAt x k _).mpr j.2⟩
      apply e.down.transverse j' ⟨s, hs, by simpa only [tangentAt_wall, j'] using hjv⟩
      rw [((D.tangentAt x).wall j').direction_support, LinearMap.mem_ker]
      rw [(D.wall j).direction_support, LinearMap.mem_ker, hsub, map_smul,
        smul_eq_mul] at hd
      simpa only [tangentAt_wall, DirectedWall.tangentAt_normal, j'] using
        (mul_eq_zero.mp hd).resolve_left ht.ne'
    regular := by
      intro s hs
      rw [hline]
      exact fun hh => e.down.regular s hs ((hsing _ (hmem hs)).mp hh) }⟩
  -- Compare simultaneous events, retaining all indexed incident walls at each time.
  refine ⟨a', b', e', rfl, rfl, ?_⟩
  rw [D.levelPathProduct_eq_wallPathProduct k _ (D.activeLabels_commute k),
    (D.tangentAt x).levelPathProduct_eq_wallPathProduct k _
      ((D.tangentAt x).activeLabels_commute k),
    Quiver.Path.wallPathProduct_toPath, Quiver.Path.wallPathProduct_toPath]
  apply segmentPathProduct_eq_of_crossingEventProduct_eq
  intro s hs
  refine (D.crossingEventProduct_eq_combinedLabel k e' hs).trans ?_
  refine Eq.trans ?_ ((D.tangentAt x).crossingEventProduct_eq_combinedLabel k e hs).symm
  obtain ⟨hreg, heq⟩ := hlabel
    (Set.add_mem_add (Set.mem_singleton x) (Set.smul_mem_smul_set (hmem hs)))
    (by simpa only [← hline] using e'.down.regular s hs)
  simp only [add_sub_cancel_left] at hreg heq
  have hc := (heq (t • (b.val - a.val))).trans
    ((D.combinedLabel_tangentAt_smul_pos k _ _ ht hreg).trans
      ((D.tangentAt x).combinedLabel_smul_pos k _ _ _ ht))
  -- Event products use the categorical tower carrier; normalize it to the BCH quotient.
  simpa only [PositiveDegrees.groupTower, hline, hsub] using hc

/-- Shrinking an admissible tangent path preserves its complete vertex list and
finite-order product. Every sufficiently small positive scale works. -/
theorem eventually_exists_levelPathProduct_tangentAt (k : ℕ)
    {a b : WallComplement (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)} (p : AdmissiblePLPath a b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∃ (a' b' : WallComplement (fun j : D.active k => (D.wall j).support))
        (p' : AdmissiblePLPath a' b'),
        a'.val = x + t • a.val ∧ b'.val = x + t • b.val ∧
        p'.vertices.map WallComplement.val =
          p.vertices.map (fun v => x + t • v.val) ∧
        D.levelPathProduct k p' = (D.tangentAt x).levelPathProduct k p := by
  induction p with
  | nil =>
    filter_upwards [D.eventually_forall_mem_support_add_smul_iff (x := x) k
      (K := {a.val}) Bornology.isBounded_singleton] with t ht
    have hoff : ∀ j : D.active k, x + t • a.val ∉ (D.wall j).support := by
      intro j hj
      obtain ⟨hxj, hjv⟩ := (ht a.val (mem_singleton _) j).mp hj
      exact a.notMem ⟨⟨j.1, hxj⟩, (D.mem_active_tangentAt x k _).mpr j.2⟩
        (by simpa only [tangentAt_wall] using hjv)
    exact ⟨⟨_, hoff⟩, ⟨_, hoff⟩, .nil, rfl, rfl, rfl, by simp⟩
  | @cons b c p e ih =>
    filter_upwards [ih, D.eventually_exists_segment_levelPathProduct_tangentAt k e]
      with t hp he
    obtain ⟨a', b', p', ha', hb', hv, hp'⟩ := hp
    obtain ⟨b'', c', e', hb'', hc', he'⟩ := he
    have hbb : b'' = b' := WallComplement.ext (hb''.trans hb'.symm)
    subst b''
    refine ⟨a', c', p'.cons e', ha', hc', ?_, ?_⟩
    · simpa only [Quiver.Path.vertices_cons, List.map_concat, hc'] using
        congrArg (fun l => l.concat (x + t • c.val)) hv
    · rw [D.levelPathProduct_cons, (D.tangentAt x).levelPathProduct_cons, he', hp']

variable {D} in
/-- Finite-order consistency passes to the incident tangent diagram at every point.
No full-hyperplane condition on the original or tangent supports is required. -/
theorem LevelConsistent.tangentAt {k : ℕ} (hD : D.LevelConsistent k) (x : V) :
    (D.tangentAt x).LevelConsistent k := by
  apply ((D.tangentAt x).levelConsistent_def k).mpr
  intro a b p q
  obtain ⟨t, hp, hq⟩ := ((D.eventually_exists_levelPathProduct_tangentAt k p).and
    (D.eventually_exists_levelPathProduct_tangentAt k q)).exists
  obtain ⟨a', b', p', ha', hb', -, hp'⟩ := hp
  obtain ⟨a'', b'', q', ha'', hb'', -, hq'⟩ := hq
  have haa : a'' = a' := WallComplement.ext (ha''.trans ha'.symm)
  have hbb : b'' = b' := WallComplement.ext (hb''.trans hb'.symm)
  subst a''
  subst b''
  exact hp'.symm.trans ((((D.levelConsistent_def k).mp hD) p' q').trans hq')

variable {D} in
/-- The incident tangent diagram of a consistent directed diagram is consistent. -/
theorem Consistent.tangentAt (hD : D.Consistent) (x : V) : (D.tangentAt x).Consistent :=
  ((D.tangentAt x).consistent_iff).mpr fun k => ((D.consistent_iff.mp hD) k).tangentAt x

end Mei.DirectedDiagram
