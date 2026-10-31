/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Convex.Polyhedron.Path.Ray
public import Mei.Geometry.Convex.Polyhedron.CrossingEvents
public import Mathlib.Order.Fin.Tuple

/-!
# Recording all encounters of straight incoming rays

A sufficiently long admissible segment, beyond which its straight continuation
misses every wall, determines an admissible realization on the entire negative
half-line. Record one parameter per simultaneous crossing event, choosing one
incident wall to supply its transverse normal. All other indexed walls remain
in the obstacle family and in the event's `crossingWalls` set; coincident walls
are neither counted as successive encounters nor discarded.

For finitely many codimension-one polyhedra and prescribed directions, a finite
exceptional arrangement supplies these realizations at every generic endpoint.
No coefficient propagation is imposed. In particular, this supplies the geometry
of an incoming line whose decoration remains unchanged at its encounters.
Stationary directions give empty encounter lists.

The construction combines `WallComplement.orderedCrossingTimes`,
`Convex.exists_ray_admissibilityArrangement` and `AdmissibleRayRealization`.
The straight incoming lines and simultaneous crossing convention follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 and §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex.WallComplement

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} (ν : ι → V →L[ℝ] ℝ) (c : ι → ℝ)

/-- Record every event on a complete straight incoming ray. The segment is read
backwards from its endpoint, so its increasing event times become decreasing
negative ray parameters. Each event retains its entire indexed wall set. -/
theorem exists_straightRayRealization_of_admissibleSegment
    (hclosed : ∀ a, IsClosed (W a))
    (hν : ∀ a, LinearMap.ker (ν a).toLinearMap = (affineSpan ℝ (W a)).direction)
    (hc : ∀ a z, z ∈ W a → ν a z = c a)
    {Q v : V} {T : ℝ} (hT : 0 < T) {x y : WallComplement W}
    (hy : y.val = Q) (hx : x.val = Q + T • v) (e : y ⟶ x)
    (htail : ∀ s ≥ T, ∀ a, Q + s • v ∉ W a)
    (C : Set V) (hC : ∀ᶠ t : ℝ in atBot, Q - t • v ∈ C) :
    let τ := orderedCrossingTimes e
    ∃ a : Fin τ.length → ι,
      (∀ j, a j ∈ crossingWalls y x (τ.get j)) ∧
      ∃ r : AdmissibleRayRealization (fun j => ν (a j)) (fun j => c (a j))
        (fun _ => v) (fun j => W (a j)) W (fun _ : Unit => singularSupport W) C Q,
        r.ray = FiniteAffineRay.straight Q v ∧
          r.parameter = Fin.cons 0 (fun j => -(τ.get j * T)) ∧
          ∀ j b, b ∈ crossingWalls y x (τ.get j) ↔
            r.ray (r.parameter j.succ) ∈ W b := by
  classical
  dsimp only
  let τ := orderedCrossingTimes e
  have hmem (j : Fin τ.length) : τ.get j ∈ orderedCrossingTimes e := List.get_mem _ _
  choose a ha using fun j => crossingWalls_nonempty e (hmem j)
  -- Convert the finite segment coordinate to negative time on the complete ray.
  have hline (s : ℝ) : AffineMap.lineMap y.val x.val s = Q + (s * T) • v := by
    rw [hy, hx, AffineMap.lineMap_apply_module']
    module
  have hpath (s : ℝ) : FiniteAffineRay.straight Q v (-(s * T)) =
      AffineMap.lineMap y.val x.val s := by
    rw [FiniteAffineRay.straight_apply, hline]
    simp [vadd_eq_add, add_comm]
  have hparam (t : ℝ) : -((-t / T) * T) = t := by simp [hT.ne']
  have hinterval {t : ℝ} (ht : t ≤ 0) (htail' : ¬ T ≤ -t) :
      -t / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hT.le, (div_le_one hT).mpr (by linarith)⟩
  have hhit (j : Fin τ.length) :
      τ.get j ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap y.val x.val (τ.get j) ∈ W (a j) :=
    (mem_crossings _ _ _ _).mp ((mem_crossingWalls _ _ _ _).mp (ha j))
  have hanti : StrictAnti (Fin.cons 0 (fun j : Fin τ.length => -(τ.get j * T))) := by
    apply (Fin.strictMono_cons (α := ℝᵒᵈ)).mpr
    constructor
    · intro j
      exact neg_neg_of_pos (mul_pos (mem_Ioo_of_mem_orderedCrossingTimes e (hmem j)).1 hT)
    · intro i j hij
      have hij' : τ.get i * T < τ.get j * T := mul_lt_mul_of_pos_right
        ((pairwise_orderedCrossingTimes e).rel_get_of_lt hij) hT
      exact neg_lt_neg hij'
  -- Reuse the straight path, recording only the distinct event times.
  -- Before the distant endpoint use tail avoidance; afterwards use the segment.
  let r : AdmissibleRayRealization (fun j => ν (a j)) (fun j => c (a j))
      (fun _ => v) (fun j => W (a j)) W (fun _ : Unit => singularSupport W) C Q := {
    ray := FiniteAffineRay.straight Q v
    parameter := Fin.cons 0 (fun j => -(τ.get j * T))
    parameter_zero := Fin.cons_zero _ _
    strictAnti_parameter := hanti
    transverse := by
      intro j hz
      apply e.down.transverse (a j) ⟨_, (hhit j).1, (hhit j).2⟩
      rw [← hν (a j)]
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hx, hy,
        map_sub, map_add, map_smul, hz, smul_zero, add_zero, sub_self]
    endpoint_eq := by simp
    directionAt_eq := by simp
    bends_recorded := by simp
    height_eq := by
      intro j
      simp only [Fin.cons_succ, hpath]
      exact hc _ _ (hhit j).2
    incidence := by
      intro j
      simpa only [Fin.cons_succ, hpath] using (hhit j).2
    avoids_walls := by
      intro b t ht hne hwall
      by_cases hfar : T ≤ -t
      · apply htail (-t) hfar b
        simpa only [FiniteAffineRay.straight_apply, vadd_eq_add, neg_smul, sub_eq_add_neg,
          add_comm] using hwall
      · have hcross : (b, -t / T) ∈ crossings y x := by
          apply (mem_crossings _ _ _ _).mpr
          refine ⟨hinterval ht.le hfar, ?_⟩
          rw [← hpath, hparam]
          exact hwall
        have hm := (mem_orderedCrossingTimes e _).mpr ⟨b, hcross⟩
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
        exact hne j (by simpa only [Fin.cons_succ, τ, hj] using (hparam t).symm)
    incoming := by
      simpa only [FiniteAffineRay.straight_apply, vadd_eq_add, neg_smul,
        sub_eq_add_neg, add_comm] using hC
    avoids_singular := by
      intro _ t ht
      by_cases hfar : T ≤ -t
      · intro hs
        obtain ⟨b, hb⟩ := mem_iUnion.mp (singularSupport_subset_iUnion W hclosed hs)
        apply htail (-t) hfar b
        simpa only [FiniteAffineRay.straight_apply, vadd_eq_add, neg_smul,
          sub_eq_add_neg, add_comm] using hb
      · rw [← hparam t, hpath]
        exact e.down.regular _ (hinterval ht hfar)
    off_walls := fun b => hy ▸ y.notMem b }
  refine ⟨a, ha, r, rfl, rfl, ?_⟩
  intro j b
  simpa only [r, Fin.cons_succ, hpath, mem_crossingWalls, mem_crossings]
    using and_iff_right (hhit j).1

/-- A finite exceptional arrangement supplies actual complete straight-ray
realizations in every prescribed direction. All encounters are recorded, source
admission is unrestricted, and the entire negative half-line avoids singular
support. No nonzero-direction assumption is needed. -/
theorem exists_straightRayRealizationArrangement [FiniteDimensional ℝ V]
    (hpoly : ∀ a, TauCeti.IsConvexPolyhedron (W a))
    (hdim : ∀ a, Module.finrank ℝ (affineSpan ℝ (W a)).direction + 1 =
      Module.finrank ℝ V)
    (hν : ∀ a, LinearMap.ker (ν a).toLinearMap = (affineSpan ℝ (W a)).direction)
    (hc : ∀ a z, z ∈ W a → ν a z = c a) (vectors : Finset V) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q → ∀ v ∈ vectors,
      ∃ (n : ℕ) (a : Fin n → ι)
        (r : AdmissibleRayRealization (fun j => ν (a j)) (fun j => c (a j))
          (fun _ => v) (fun j => W (a j)) W
          (fun _ : Unit => singularSupport W) univ Q),
        r.ray = FiniteAffineRay.straight Q v := by
  obtain ⟨A, hA⟩ := exists_ray_admissibilityArrangement W hpoly hdim vectors
  refine ⟨A, fun Q hQ v hv => ?_⟩
  obtain ⟨y, hy, hsegments⟩ := hA Q hQ
  have htail : ∀ᶠ T : ℝ in atTop, ∀ s ≥ T, ∀ a, Q + s • v ∉ W a := by
    filter_upwards [eventually_forall_ge_atTop.mpr (hsegments v hv)] with T hT s hs
    obtain ⟨x, hx, _⟩ := hT s hs
    exact fun a => hx ▸ x.notMem a
  obtain ⟨T, hT, htail, x, hx, e⟩ :=
    (eventually_gt_atTop (0 : ℝ) |>.and (htail.and (hsegments v hv))).exists
  obtain ⟨a, _, r, hr, _⟩ := exists_straightRayRealization_of_admissibleSegment ν c
    (fun a => (hpoly a).isClosed) hν hc hT hy hx (Quiver.reverse ⟨e⟩) htail
    univ (Eventually.of_forall fun _ => mem_univ _)
  exact ⟨_, a, r, hr⟩

end Mei.Convex
