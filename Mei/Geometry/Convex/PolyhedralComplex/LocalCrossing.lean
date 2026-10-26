/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Affine.Segment

/-!
# Isolating a regular wall crossing

Near a point on a wall outside singular support, an admissible segment meeting
that wall has exactly one crossing. Every sufficiently short segment through
the point in any transverse direction is admissible and realizes this crossing.
This isolates the individual factors of path products before comparing them
with endpoint transport.

The proof uses regular-wall uniqueness and the openness of segment avoidance
from `IsClosed.isOpen_setOf_lineMap_notMem`. Crossing lists are characterized
by `FinitePolyhedralComplex.orderedCrossings_eq_iff`.
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h) {P : C.walls} {θ : V}

/-- Near a regular wall point, short segments avoid every other wall. -/
theorem eventually_lineMap_notMem_other_walls (hθP : θ ∈ (P : Set V))
    (hθ : θ ∉ singularSupport (fun Q : C.walls => (Q : Set V))) :
    ∀ᶠ q : V × V in 𝓝 (θ, θ), ∀ Q : C.walls, Q ≠ P →
      ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap q.1 q.2 t ∉ (Q : Set V) := by
  classical
  have hQ (Q : C.walls) : ∀ᶠ q : V × V in 𝓝 (θ, θ),
      Q ≠ P → ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap q.1 q.2 t ∉ (Q : Set V) := by
    by_cases he : Q = P
    · exact Eventually.of_forall fun _ hne => (hne he).elim
    · have hnot : θ ∉ (Q : Set V) := fun hQ =>
        he (C.eq_of_mem_wall_of_notMem_singularSupport hQ hθP hθ)
      have hc := (C.isConvexPolyhedron (C.mem_cells_of_mem_walls Q.property)).isClosed
      have hbase : (θ, θ) ∈ {q : V × V |
          ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap q.1 q.2 t ∉ (Q : Set V)} := by
        simpa using fun (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) => hnot
      have hn := hc.isOpen_setOf_lineMap_notMem.mem_nhds hbase
      filter_upwards [hn] with q hq
      exact fun _ => hq
  exact eventually_all.mpr hQ

/-- Close to a regular point on a wall, a segment crossing that wall crosses
no other wall; its ordered crossing list consists of that single event. -/
theorem eventually_orderedCrossings_eq_singleton (hθP : θ ∈ (P : Set V))
    (hθ : θ ∉ singularSupport (fun Q : C.walls => (Q : Set V))) :
    ∀ᶠ q : V × V in 𝓝 (θ, θ),
      ∀ (x y : WallComplement (fun Q : C.walls => (Q : Set V))) (e : x ⟶ y),
        x.val = q.1 → y.val = q.2 → ∀ t,
          (P, t) ∈ WallComplement.crossings x y → C.orderedCrossings e = [(P, t)] := by
  classical
  filter_upwards [C.eventually_lineMap_notMem_other_walls hθP hθ] with q hq x y e hx hy t ht
  apply ((C.orderedCrossings_eq_iff e [(P, t)]).mpr ⟨by simp, ?_⟩).symm
  intro a
  constructor
  · intro ha
    simpa only [List.mem_singleton.mp ha] using ht
  · intro ha
    have ha' := (WallComplement.mem_crossings x y a.1 a.2).mp ha
    have he : a.1 = P := by
      by_contra hne
      exact hq a.1 hne a.2 ha'.1 (by simpa only [hx, hy] using ha'.2)
    obtain ⟨Q, s⟩ := a
    dsimp only at he
    subst Q
    have hs := e.down.subsingleton_crossing P ha'
      ((WallComplement.mem_crossings x y P t).mp ht)
    exact List.mem_singleton.mpr (Prod.ext rfl hs)

/-- Every sufficiently short segment through a regular wall point in a transverse
vector direction is admissible and crosses exactly that wall, at its midpoint.
The segment runs from `θ + a • v` to `θ - a • v`, with `a` tending to zero from above. -/
theorem eventually_exists_orderedCrossings_eq_singleton (hθP : θ ∈ (P : Set V))
    (hθ : θ ∉ singularSupport (fun Q : C.walls => (Q : Set V)))
    {v : V} (hv : v ∉ (affineSpan ℝ (P : Set V)).direction) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (fun Q : C.walls => (Q : Set V))) (e : x ⟶ y),
        x.val = θ + a • v ∧ y.val = θ - a • v ∧
        C.orderedCrossings e = [(P, (1 / 2 : ℝ))] := by
  classical
  let := h.finiteDimensional
  have hclosed (Q : C.walls) : IsClosed (Q : Set V) :=
    (C.isConvexPolyhedron (C.mem_cells_of_mem_walls Q.property)).isClosed
  have hreg : ∀ᶠ q : V × V in 𝓝 (θ, θ), ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap q.1 q.2 t ∉ singularSupport (fun Q : C.walls => (Q : Set V)) :=
    (isClosed_singularSupport _ hclosed).isOpen_setOf_lineMap_notMem.mem_nhds
      (by simpa using fun (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) => hθ)
  have hc : Continuous (fun a : ℝ => (θ + a • v, θ - a • v)) := by fun_prop
  have ht : Tendsto (fun a : ℝ => (θ + a • v, θ - a • v)) (𝓝 0) (𝓝 (θ, θ)) := by
    simpa using hc.tendsto 0
  have hnear := ht.eventually (hreg.and ((C.eventually_lineMap_notMem_other_walls hθP hθ).and
    (C.eventually_orderedCrossings_eq_singleton hθP hθ)))
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha ha0
  have ha0 : 0 < a := ha0
  -- A nonzero transverse displacement cannot lie in the wall’s affine span.
  have hnot {b : ℝ} (hb : b ≠ 0) : θ + b • v ∉ (P : Set V) := by
    intro hp
    have hd := (affineSpan ℝ (P : Set V)).vsub_mem_direction
      (subset_affineSpan ℝ _ hp) (subset_affineSpan ℝ _ hθP)
    have hsmul : b • v ∈ (affineSpan ℝ (P : Set V)).direction := by simpa using hd
    exact hv ((Submodule.smul_mem_iff _ hb).mp hsmul)
  -- Avoid the remaining walls and singular support uniformly along the segment.
  let x : WallComplement (fun Q : C.walls => (Q : Set V)) :=
    ⟨θ + a • v, fun Q hQ => by
      by_cases he : Q = P
      · subst Q; exact hnot ha0.ne' hQ
      · exact ha.2.1 Q he 0 ⟨le_rfl, zero_le_one⟩ (by simpa using hQ)⟩
  let y : WallComplement (fun Q : C.walls => (Q : Set V)) :=
    ⟨θ - a • v, fun Q hQ => by
      by_cases he : Q = P
      · subst Q; exact hnot (neg_ne_zero.mpr ha0.ne') (by simpa [sub_eq_add_neg] using hQ)
      · exact ha.2.1 Q he 1 ⟨zero_le_one, le_rfl⟩ (by simpa using hQ)⟩
  have hdir : y.val - x.val ∉ (affineSpan ℝ (P : Set V)).direction := by
    have he : y.val - x.val = (-2 * a) • v := by dsimp [x, y]; module
    rw [he]
    exact fun hd => hv ((Submodule.smul_mem_iff _ (by positivity : -2 * a ≠ 0)).mp hd)
  let e : x ⟶ y := ⟨{
    transverse := fun Q ⟨t, ht, hQ⟩ => by
      by_cases he : Q = P
      · subst Q; exact hdir
      · exact (ha.2.1 Q he t ht hQ).elim
    regular := ha.1 }⟩
  refine ⟨x, y, e, rfl, rfl, ha.2.2 x y e rfl rfl (1 / 2) ?_⟩
  rw [WallComplement.mem_crossings]
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  have he : AffineMap.lineMap x.val y.val (1 / 2 : ℝ) = θ := by
    simp only [AffineMap.lineMap_apply_module', x, y]
    module
  exact he ▸ hθP

end Mei.FinitePolyhedralComplex
