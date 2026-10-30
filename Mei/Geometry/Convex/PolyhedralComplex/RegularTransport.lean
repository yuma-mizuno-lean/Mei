/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.Path.Hyperplane

/-!
# Local endpoint independence of crossing words

On a convex region meeting only one wall, where that wall agrees with its
supporting hyperplane, a polygonal crossing word is a power of the wall's
generator. Its exponent is the difference of the endpoint half-space indicators.
Repeated visits therefore cancel even in the free group.

Every point outside the singular support of a finite polyhedral complex has
a ball with endpoint-independent crossing words. This includes points on
regular walls, as well as points in their complement. These balls provide the
regular neighborhoods used when decomposing a polygonal homotopy into local
crossing relations; arbitrary group-valued labels inherit the same independence.

The construction uses `FinitePolyhedralComplex.exists_isolating_ball`,
`Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior`, and the local hyperplane
crossing criterion `WallComplement.exists_crossing_iff_of_hyperplane`.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

private theorem segmentCrossingWord_eq_zpow_of_local_wall
    (ν : C.walls → V →ₗ[ℝ] ℝ) (P : C.walls) (b : ℝ)
    {U : Set V} (hU : Convex ℝ U)
    (hwall : ∀ z ∈ U, z ∈ (P : Set V) ↔ ν P z = b)
    (hother : ∀ Q : C.walls, Q ≠ P → Disjoint U (Q : Set V))
    (e : x ⟶ y) (hx : x.val ∈ U) (hy : y.val ∈ U) :
    C.segmentCrossingWord ν e = FreeGroup.of P ^
      ((if b < ν P x.val then 1 else 0 : ℤ) -
        (if b < ν P y.val then 1 else 0)) := by
  classical
  have hseg := hU.segment_subset hx hy
  have hidx {Q : C.walls} {t : ℝ} (ht : (Q, t) ∈ WallComplement.crossings x y) : Q = P := by
    by_contra hne
    obtain ⟨htI, htQ⟩ := (WallComplement.mem_crossings x y Q t).mp ht
    exact Set.disjoint_left.mp (hother Q hne)
      (hseg (lineMap_mem_segment ℝ _ _ htI)) htQ
  let f : V →ᵃ[ℝ] ℝ := (ν P).toAffineMap - AffineMap.const ℝ V b
  have hc := WallComplement.exists_crossing_iff_of_hyperplane x y f (j := P)
    (fun z hz => (hwall z (hseg hz)).trans (by simp [f, sub_eq_zero]))
  simp only [f, AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
    AffineMap.const_apply, sub_pos] at hc
  by_cases hcross : ∃ t, (P, t) ∈ WallComplement.crossings x y
  · obtain ⟨t, ht⟩ := hcross
    have hl : C.orderedCrossings e = [(P, t)] := by
      apply ((C.orderedCrossings_eq_iff e _).mpr ⟨by simp, ?_⟩).symm
      intro ⟨Q, s⟩
      constructor
      · rintro he
        exact (List.mem_singleton.mp he).symm ▸ ht
      · intro hs
        have hQP := hidx hs
        subst Q
        exact List.mem_singleton.mpr (Prod.ext rfl
          (e.down.subsingleton_crossing P
            ((WallComplement.mem_crossings x y P s).mp hs)
            ((WallComplement.mem_crossings x y P t).mp ht)))
    have hsign := hc.mp ⟨t, ht⟩
    simp only [segmentCrossingWord_def, hl, List.reverse_singleton, List.map_singleton,
      List.prod_singleton, crossingLetter_def, map_sub]
    split_ifs <;> norm_num <;> grind
  · have hempty : WallComplement.crossings x y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨Q, t⟩ ht
      have hQP := hidx ht
      subst Q
      exact hcross ⟨t, ht⟩
    rw [C.segmentCrossingWord_eq_one ν e hempty]
    have hside := not_not.mp (mt hc.mpr hcross)
    simp only [hside, sub_self, zpow_zero]

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Within a convex region where the only wall is a full hyperplane slice,
the word is the wall generator to the difference of endpoint-side indicators.
The path may cross the wall arbitrarily often. -/
theorem crossingWord_eq_zpow_of_local_wall (p : AdmissiblePLPath x y)
    (ν : C.walls → V →ₗ[ℝ] ℝ) (P : C.walls) (b : ℝ)
    {U : Set V} (hU : Convex ℝ U)
    (hwall : ∀ z ∈ U, z ∈ (P : Set V) ↔ ν P z = b)
    (hother : ∀ Q : C.walls, Q ≠ P → Disjoint U (Q : Set V))
    (hp : ∀ z ∈ p.vertices, z.val ∈ U) :
    p.crossingWord ν = FreeGroup.of P ^
      ((if b < ν P x.val then 1 else 0 : ℤ) -
        (if b < ν P y.val then 1 else 0)) := by
  induction p with
  | nil => simp
  | @cons y z p e ih =>
    have hp' : ∀ v ∈ p.vertices, v.val ∈ U :=
      fun v hv => hp v ((mem_vertices_cons p e).mpr (Or.inl hv))
    rw [crossingWord_cons,
      Mei.FinitePolyhedralComplex.segmentCrossingWord_eq_zpow_of_local_wall
        ν P b hU hwall hother e (hp' y p.end_mem_vertices)
        (hp z ((mem_vertices_cons p e).mpr (Or.inr rfl))), ih hp', ← zpow_add]
    congr 1
    omega

end Quiver.Path

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Every point outside singular support has a ball in which admissible
polygonal crossing words depend only on the endpoints. The paths need only
have their vertices in the ball; convexity keeps all their segments there. -/
theorem exists_ball_crossingWord_eq (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    {θ : V} (hθ : θ ∉ singularSupport (fun P : C.walls => (P : Set V))) :
    ∃ r > 0, ∀ (x y : WallComplement (fun P : C.walls => (P : Set V)))
      (p q : AdmissiblePLPath x y),
      (∀ z ∈ p.vertices, z.val ∈ Metric.ball θ r) →
      (∀ z ∈ q.vertices, z.val ∈ Metric.ball θ r) → p.crossingWord ν = q.crossingWord ν := by
  classical
  have := h.finiteDimensional
  by_cases hwall : ∃ P : C.walls, θ ∈ (P : Set V)
  · -- A regular wall is locally its affine span, and every other wall misses a ball.
    obtain ⟨P, hP⟩ := hwall
    have hint := mem_intrinsicInterior_of_notMem_singularSupport hP hθ
    obtain ⟨δ, hδ, hδmem⟩ := Metric.mem_nhdsWithin_iff.mp
      (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hint)
    obtain ⟨ε, hε, -, -, hotherε, -⟩ := C.exists_isolating_ball P.property hint
    -- Express that affine span by the given coorientation to compute both words.
    have hplane (z : V) : z ∈ affineSpan ℝ (P : Set V) ↔ ν P z = ν P θ := by
      rw [← (affineSpan ℝ (P : Set V)).mk'_eq (subset_affineSpan ℝ _ hP),
        AffineSubspace.mem_mk', ← hν P, LinearMap.mem_ker]
      simp only [vsub_eq_sub, map_sub, sub_eq_zero]
    have hlocal (z : V) (hz : z ∈ Metric.ball θ (min δ ε)) :
        z ∈ (P : Set V) ↔ ν P z = ν P θ := by
      constructor
      · exact fun hzP => (hplane z).mp (subset_affineSpan ℝ _ hzP)
      · exact fun he => hδmem ⟨Metric.ball_subset_ball (min_le_left _ _) hz, (hplane z).mpr he⟩
    have hother (Q : C.walls) (hne : Q ≠ P) :
        Disjoint (Metric.ball θ (min δ ε)) (Q : Set V) :=
      (hotherε Q Q.property (Subtype.coe_ne_coe.mpr hne)).mono_left
        (Metric.ball_subset_ball (min_le_right _ _))
    refine ⟨min δ ε, lt_min hδ hε, fun x y p q hp hq => ?_⟩
    rw [p.crossingWord_eq_zpow_of_local_wall ν P (ν P θ) (convex_ball θ _) hlocal hother hp,
      q.crossingWord_eq_zpow_of_local_wall ν P (ν P θ) (convex_ball θ _) hlocal hother hq]
  · -- Off all walls, a common ball has no crossings at all.
    have hmiss : ∀ᶠ z in 𝓝 θ, ∀ P : C.walls, z ∉ (P : Set V) := by
      filter_upwards [(locallyFinite_of_finite (fun P : C.walls => (P : Set V))).eventually_subset
        (fun P => (C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property)).isClosed) θ]
        with z hz P hzP
      exact hwall ⟨P, hz hzP⟩
    obtain ⟨r, hr, hmem⟩ := Metric.mem_nhds_iff.mp hmiss
    have hword {x y : WallComplement (fun P : C.walls => (P : Set V))}
        (p : AdmissiblePLPath x y) (hp : ∀ z ∈ p.vertices, z.val ∈ Metric.ball θ r) :
        p.crossingWord ν = 1 := by
      induction p with
      | nil => simp
      | @cons y z p e ih =>
        have hp' : ∀ v ∈ p.vertices, v.val ∈ Metric.ball θ r :=
          fun v hv => hp v ((Quiver.Path.mem_vertices_cons p e).mpr (Or.inl hv))
        have he : WallComplement.crossings y z = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro ⟨P, t⟩ ht
          obtain ⟨htI, htP⟩ := (WallComplement.mem_crossings y z P t).mp ht
          exact hmem ((convex_ball θ r).segment_subset (hp' y p.end_mem_vertices)
            (hp z ((Quiver.Path.mem_vertices_cons p e).mpr (Or.inr rfl)))
            (lineMap_mem_segment ℝ _ _ htI)) P htP
        rw [Quiver.Path.crossingWord_cons, C.segmentCrossingWord_eq_one ν e he, ih hp', mul_one]
    exact ⟨r, hr, fun _ _ p q hp hq => (hword p hp).trans (hword q hq).symm⟩

/-- Every point off singular support has a ball in which every admissible loop has trivial
crossing word. -/
theorem exists_ball_crossingWord_loop_eq_one (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    {θ : V} (hθ : θ ∉ singularSupport (fun P : C.walls => (P : Set V))) :
    ∃ r > 0, ∀ (y : WallComplement (fun P : C.walls => (P : Set V)))
      (p : AdmissiblePLPath y y), (∀ w ∈ p.vertices, w.val ∈ Metric.ball θ r) →
        p.crossingWord ν = 1 := by
  obtain ⟨r, hr, hword⟩ := C.exists_ball_crossingWord_eq ν hν hθ
  refine ⟨r, hr, fun y p hp => ?_⟩
  -- Compare with the constant loop at the base point.
  refine (hword y y p .nil hp fun w hw => ?_).trans (Quiver.Path.crossingWord_nil ν)
  rw [show w = y by simpa using hw]
  exact hp _ p.start_mem_vertices

end Mei.FinitePolyhedralComplex
