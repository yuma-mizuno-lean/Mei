/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Analysis.Convex.Intrinsic
public import Mei.Geometry.Affine.Codimension
public import Mei.Geometry.Convex.Polyhedron.Path.Chamber
public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.PolyhedralComplex.Strata

/-!
# The chambers on the two sides of a cooriented wall

Let `P` be a wall of a finite polyhedral complex, cooriented by a linear functional `ν`
whose kernel is the direction of `P`. All points just off the relative interior of `P`
on the side where `ν` increases lie in one chamber of the wall complement, the
*positive chamber* of `P`; the *negative chamber* is the positive chamber of `-ν`. This
holds for every relative interior point and every positively transverse velocity.
Consequently an admissible segment crossing exactly one wall, with positive normal
velocity, runs from the negative to the positive chamber of that wall.

Chambers are the connected components of the wall complement
(`Mei.Convex.WallComplement.Chamber`), so no covering hypothesis on the complex is
needed, and the two chambers of a wall may coincide. Near a relative interior point, a
ball meets no other wall (`FinitePolyhedralComplex.exists_isolating_ball`); its open
half on the positive side is convex and avoids every wall. Overlapping half-balls along
the preconnected relative interior give one chamber. When the complex covers a
neighborhood of the wall, the full cells of
`FinitePolyhedralComplex.exists_cooriented_wall_chambers` have these chambers as
interiors.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} (C : FinitePolyhedralComplex h)

/-- Near a relative interior point of a wall, a ball meets no other wall. -/
theorem exists_ball_eq_wall_of_mem_intrinsicInterior (P : C.walls) {q : V}
    (hq : q ∈ intrinsicInterior ℝ (P : Set V)) :
    ∃ r > 0, ∀ Q : C.walls, ∀ z ∈ Metric.ball q r, z ∈ (Q : Set V) → Q = P := by
  obtain ⟨r, hr, -, -, hdisj, -⟩ := C.exists_isolating_ball P.property hq
  refine ⟨r, hr, fun Q z hz hzQ => ?_⟩
  by_contra hne
  exact disjoint_left.mp (hdisj Q Q.property fun he => hne (Subtype.ext he)) hz hzQ

variable {C}

/-- The chamber `c` contains the positive half of a small ball centered at `q`. -/
private def IsPositiveSideAt (ν : V →ₗ[ℝ] ℝ) (q : V)
    (c : Chamber (fun P : C.walls => (P : Set V))) : Prop :=
  ∃ r > 0, ∀ z ∈ Metric.ball q r, ν q < ν z → z ∈ c.carrier

/-- Small positive multiples of a velocity stay in any ball around the base point. -/
private theorem eventually_add_smul_mem_ball {q v : V} {r : ℝ} (hr : 0 < r) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ Metric.ball q r := by
  apply nhdsWithin_le_nhds
  have hc : Continuous fun t : ℝ => q + t • v := continuous_const.add
    (continuous_id.smul continuous_const)
  exact (hc.tendsto' 0 q (by simp)).eventually
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

/-- On a positive side, the chamber contains all short positively transverse rays. -/
private theorem IsPositiveSideAt.eventually {ν : V →ₗ[ℝ] ℝ} {q : V}
    {c : Chamber (fun P : C.walls => (P : Set V))} (hc : IsPositiveSideAt ν q c)
    {v : V} (hv : 0 < ν v) : ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ c.carrier := by
  obtain ⟨r, hr, hball⟩ := hc
  filter_upwards [eventually_add_smul_mem_ball (v := v) hr, self_mem_nhdsWithin] with t ht htp
  refine hball _ ht ?_
  rw [map_add, map_smul, smul_eq_mul]
  exact lt_add_of_pos_right _ (mul_pos htp hv)

/-- A cooriented wall is cut out by a nonzero normal. -/
private theorem exists_normal_eq_one {P : C.walls} {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) : ∃ v : V, ν v = 1 := by
  have hne : ν ≠ 0 := by
    intro hz
    have hd := C.finrank_direction_add_one_of_mem_walls P.property
    rw [← hν, hz, LinearMap.ker_zero, finrank_top] at hd
    omega
  exact LinearMap.surjective hne 1

/-- A positive side at a point is unique. -/
private theorem IsPositiveSideAt.unique {P : C.walls} {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) {q : V}
    {c c' : Chamber (fun P : C.walls => (P : Set V))} (hc : IsPositiveSideAt ν q c)
    (hc' : IsPositiveSideAt ν q c') : c = c' := by
  obtain ⟨v, hv⟩ := exists_normal_eq_one hν
  obtain ⟨t, ht, ht'⟩ := ((hc.eventually (v := v) (by rw [hv]; exact one_pos)).and
    (hc'.eventually (v := v) (by rw [hv]; exact one_pos))).exists
  exact eq_of_mem_carrier ht ht'

/-- At a relative interior point of a wall, the positive half of a small ball lies in
one chamber. -/
private theorem exists_isPositiveSideAt {P : C.walls} {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) {q : V}
    (hq : q ∈ intrinsicInterior ℝ (P : Set V)) :
    ∃ c : Chamber (fun Q : C.walls => (Q : Set V)), IsPositiveSideAt ν q c := by
  obtain ⟨r, hr, hwall⟩ := C.exists_ball_eq_wall_of_mem_intrinsicInterior P hq
  have hqP : q ∈ (P : Set V) := intrinsicInterior_subset hq
  -- The open positive half-ball is convex and misses every wall.
  let A := Metric.ball q r ∩ {z | ν q < ν z}
  have hA : IsPreconnected A :=
    ((convex_ball q r).inter (convex_halfSpace_gt (f := ⇑ν) ν.isLinear (ν q))).isPreconnected
  have hAW : ∀ a ∈ A, ∀ Q : C.walls, a ∉ (Q : Set V) := by
    rintro a ⟨ha, hlt⟩ Q haQ
    obtain rfl := hwall Q a ha haQ
    exact hlt.ne' (ν.apply_eq_of_direction_le_ker hν.ge haQ hqP)
  obtain ⟨v, hv⟩ := exists_normal_eq_one hν
  obtain ⟨t, ht, htp⟩ := ((eventually_add_smul_mem_ball (v := v) hr).and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t)).exists
  have hzA : q + t • v ∈ A := ⟨ht, by simpa [hv] using htp⟩
  let z : {x : V | ∀ Q : C.walls, x ∉ (Q : Set V)} := ⟨q + t • v, hAW _ hzA⟩
  have hz : q + t • v ∈ (ConnectedComponents.mk z).carrier :=
    ConnectedComponents.mem_carrier_iff.mpr ⟨z.property, rfl⟩
  exact ⟨ConnectedComponents.mk z, r, hr, fun a ha hlt =>
    subset_carrier_of_isPreconnected hA hAW hzA hz ⟨ha, hlt⟩⟩

/-- A positive side persists at nearby relative interior points of the wall. -/
private theorem IsPositiveSideAt.of_mem_ball {P : C.walls} {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) {q q' : V}
    (hq : q ∈ (P : Set V)) (hq' : q' ∈ (P : Set V))
    {c : Chamber (fun P : C.walls => (P : Set V))} {r : ℝ}
    (hball : ∀ z ∈ Metric.ball q r, ν q < ν z → z ∈ c.carrier)
    (hqq' : q' ∈ Metric.ball q r) : IsPositiveSideAt ν q' c := by
  refine ⟨r - dist q' q, sub_pos.mpr (Metric.mem_ball.mp hqq'), fun z hz hlt => ?_⟩
  refine hball z ?_ (by rwa [ν.apply_eq_of_direction_le_ker hν.ge hq' hq] at hlt)
  rw [Metric.mem_ball] at hz ⊢
  linarith [dist_triangle z q' q]

/-- A cooriented wall has a unique chamber containing every short positively
transverse ray from its relative interior. -/
theorem existsUnique_positiveChamber (P : C.walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) :
    ∃! c : Chamber (fun P : C.walls => (P : Set V)),
      ∀ q ∈ intrinsicInterior ℝ (P : Set V), ∀ v : V, 0 < ν v →
        ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ c.carrier := by
  have := h.finiteDimensional
  have hPC := C.mem_cells_of_mem_walls P.property
  have hconv : Convex ℝ (P : Set V) := (C.isConvexPolyhedron hPC).convex
  obtain ⟨q₀, hq₀⟩ := (C.nonempty _ hPC).intrinsicInterior hconv
  obtain ⟨v, hv⟩ := exists_normal_eq_one hν
  have hv' : 0 < ν v := by rw [hv]; exact one_pos
  -- The positive side is locally constant along the preconnected relative interior.
  let f : intrinsicInterior ℝ (P : Set V) → Chamber (fun P : C.walls => (P : Set V)) :=
    fun q => (exists_isPositiveSideAt hν q.property).choose
  have hf : ∀ q, IsPositiveSideAt ν q.val (f q) :=
    fun q => (exists_isPositiveSideAt hν q.property).choose_spec
  have hloc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).mpr fun q => ?_
    obtain ⟨r, hr, hball⟩ := hf q
    filter_upwards [(Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
      (show q.val ∈ Metric.ball q.val r from Metric.mem_ball_self hr)] with q' hq'
    exact (hf q').unique hν (IsPositiveSideAt.of_mem_ball hν
      (intrinsicInterior_subset q.property) (intrinsicInterior_subset q'.property) hball hq')
  have : PreconnectedSpace (intrinsicInterior ℝ (P : Set V)) :=
    isPreconnected_iff_preconnectedSpace.mp (Convex.intrinsicInterior hconv).isPreconnected
  refine ⟨f ⟨q₀, hq₀⟩, fun q hq w hw => ?_, fun c hc => ?_⟩
  · rw [hloc.apply_eq_of_preconnectedSpace ⟨q₀, hq₀⟩ ⟨q, hq⟩]
    exact (hf ⟨q, hq⟩).eventually hw
  · obtain ⟨t, ht, ht'⟩ := ((hc q₀ hq₀ v hv').and ((hf ⟨q₀, hq₀⟩).eventually hv')).exists
    exact eq_of_mem_carrier ht ht'

variable (C) in
/-- The chamber on the side of a wall where its coorientation increases. -/
def positiveChamber (P : C.walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) :
    Chamber (fun P : C.walls => (P : Set V)) :=
  (existsUnique_positiveChamber P ν hν).exists.choose

variable (C) in
/-- The chamber on the side of a wall where its coorientation decreases. -/
def negativeChamber (P : C.walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) :
    Chamber (fun P : C.walls => (P : Set V)) :=
  C.positiveChamber P (-ν) (by rwa [LinearMap.ker_neg])

/-- Short positively transverse rays from the relative interior of a wall enter its
positive chamber. -/
theorem eventually_add_smul_mem_positiveChamber {P : C.walls} {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) {q : V}
    (hq : q ∈ intrinsicInterior ℝ (P : Set V)) {v : V} (hv : 0 < ν v) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ (C.positiveChamber P ν hν).carrier :=
  (existsUnique_positiveChamber P ν hν).exists.choose_spec q hq v hv

/-- Short negatively transverse rays from the relative interior of a wall enter its
negative chamber. -/
theorem eventually_sub_smul_mem_negativeChamber {P : C.walls} {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) {q : V}
    (hq : q ∈ intrinsicInterior ℝ (P : Set V)) {v : V} (hv : 0 < ν v) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, q - t • v ∈ (C.negativeChamber P ν hν).carrier := by
  unfold negativeChamber
  simpa only [smul_neg, ← sub_eq_add_neg] using
    eventually_add_smul_mem_positiveChamber (C := C) (P := P) (ν := -ν)
      (by rwa [LinearMap.ker_neg]) hq (v := -v) (by simpa using hv)

/-- The positive chamber is characterized by a single short positively transverse ray. -/
theorem eq_positiveChamber_of_frequently {P : C.walls} {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) {q : V}
    (hq : q ∈ intrinsicInterior ℝ (P : Set V)) {v : V} (hv : 0 < ν v)
    {c : Chamber (fun P : C.walls => (P : Set V))}
    (hc : ∃ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ c.carrier) : c = C.positiveChamber P ν hν := by
  obtain ⟨t, ht, ht'⟩ := (hc.and_eventually
    (eventually_add_smul_mem_positiveChamber hν hq hv)).exists
  exact eq_of_mem_carrier ht ht'

/-- An admissible segment crossing exactly one wall, with positive normal velocity,
starts in the negative chamber of that wall and ends in its positive chamber. -/
theorem chamber_eq_of_crossings_eq_singleton
    {x y : WallComplement (fun P : C.walls => (P : Set V))} (e : x ⟶ y) {P : C.walls}
    {t : ℝ} (he : WallComplement.crossings x y = {(P, t)}) {ν : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction)
    (hv : 0 < ν (y.val - x.val)) :
    chamber x = C.negativeChamber P ν hν ∧ chamber y = C.positiveChamber P ν hν := by
  have hmem : (P, t) ∈ WallComplement.crossings x y := he ▸ rfl
  obtain ⟨ht, hP⟩ := (WallComplement.mem_crossings x y P t).mp hmem
  obtain ⟨ht', hq⟩ := e.down.crossing_mem_intrinsicInterior ht hP
  set q := AffineMap.lineMap x.val y.val t
  -- Points of the segment other than the crossing point avoid every wall.
  have hfree : ∀ u ∈ Icc (0 : ℝ) 1, u ≠ t →
      ∀ Q : C.walls, AffineMap.lineMap x.val y.val u ∉ (Q : Set V) := by
    intro u hu hut Q hQ
    have hm : (Q, u) ∈ WallComplement.crossings x y :=
      (WallComplement.mem_crossings x y Q u).mpr ⟨hu, hQ⟩
    rw [he, mem_singleton_iff, Prod.mk.injEq] at hm
    exact hut hm.2
  have hshift (s : ℝ) : AffineMap.lineMap x.val y.val (t + s) = q + s • (y.val - x.val) := by
    simp only [q, AffineMap.lineMap_apply_module', add_smul]
    abel
  have hshift' (s : ℝ) :
      AffineMap.lineMap x.val y.val (t - s) = q - s • (y.val - x.val) := by
    simp only [q, AffineMap.lineMap_apply_module', sub_smul]
    abel
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < min t (1 - t) :=
    nhdsWithin_le_nhds (gt_mem_nhds (lt_min ht'.1 (sub_pos.mpr ht'.2)))
  obtain ⟨s, ⟨hneg, hpos⟩, hs, hs0⟩ :=
    (((eventually_sub_smul_mem_negativeChamber hν hq hv).and
      (eventually_add_smul_mem_positiveChamber hν hq hv)).and
        (hsmall.and self_mem_nhdsWithin)).exists
  have hst : s < t := hs.trans_le (min_le_left _ _)
  have hst' : s < 1 - t := hs.trans_le (min_le_right _ _)
  constructor
  · refine chamber_eq_of_isPreconnected
      (isPreconnected_Icc.image _ AffineMap.lineMap_continuous.continuousOn) ?_
      ⟨0, ⟨le_rfl, by linarith⟩, AffineMap.lineMap_apply_zero _ _⟩
      ⟨t - s, ⟨by linarith, le_rfl⟩, rfl⟩ (by rwa [hshift'])
    rintro _ ⟨u, hu, rfl⟩
    exact hfree u ⟨hu.1, by linarith [hu.2]⟩ (by linarith [hu.2])
  · refine chamber_eq_of_isPreconnected
      (isPreconnected_Icc.image _ AffineMap.lineMap_continuous.continuousOn) ?_
      ⟨1, ⟨by linarith, le_rfl⟩, AffineMap.lineMap_apply_one _ _⟩
      ⟨t + s, ⟨le_rfl, by linarith⟩, rfl⟩ (by rwa [hshift])
    rintro _ ⟨u, hu, rfl⟩
    exact hfree u ⟨by linarith [hu.1], hu.2⟩ (by linarith [hu.1])

end Mei.FinitePolyhedralComplex
