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
that wall has exactly one crossing. This isolates the individual factors of
path products before comparing them with endpoint transport.

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

/-- Close to a regular point on a wall, a segment crossing that wall crosses
no other wall; its ordered crossing list consists of that single event. -/
theorem eventually_orderedCrossings_eq_singleton (hθP : θ ∈ (P : Set V))
    (hθ : θ ∉ singularSupport (fun Q : C.walls => (Q : Set V))) :
    ∀ᶠ q : V × V in 𝓝 (θ, θ),
      ∀ (x y : WallComplement (fun Q : C.walls => (Q : Set V))) (e : x ⟶ y),
        x.val = q.1 → y.val = q.2 → ∀ t,
          (P, t) ∈ WallComplement.crossings x y → C.orderedCrossings e = [(P, t)] := by
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
  filter_upwards [eventually_all.mpr hQ] with q hq x y e hx hy t ht
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

end Mei.FinitePolyhedralComplex
