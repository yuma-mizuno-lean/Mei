/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.Path.LocalCrossing

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
  filter_upwards [eventually_forall_lineMap_notMem_of_notMem
    (fun Q : C.walls =>
      (C.isConvexPolyhedron (C.mem_cells_of_mem_walls Q.property)).isClosed) θ]
    with q hq Q hne
  exact hq Q (fun hQ => hne (C.eq_of_mem_wall_of_notMem_singularSupport hQ hθP hθ))

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
  have hQ (Q : C.walls) : θ ∈ (Q : Set V) ↔ Q = P :=
    ⟨fun hQ => C.eq_of_mem_wall_of_notMem_singularSupport hQ hθP hθ,
      fun he => he ▸ hθP⟩
  have htrans (Q : C.walls) (hθQ : θ ∈ (Q : Set V)) :
      -v ∉ (affineSpan ℝ (Q : Set V)).direction := by
    obtain rfl := (hQ Q).mp hθQ
    simpa using hv
  filter_upwards [WallComplement.eventually_exists_crossings_iff
    (fun Q : C.walls =>
      (C.isConvexPolyhedron (C.mem_cells_of_mem_walls Q.property)).isClosed) hθ htrans]
    with a ha
  obtain ⟨x, y, e, hx, hy, hcross⟩ := ha
  refine ⟨x, y, e, by simpa using hx, by simpa [sub_eq_add_neg] using hy, ?_⟩
  apply ((C.orderedCrossings_eq_iff e [(P, (1 / 2 : ℝ))]).mpr ⟨by simp, ?_⟩).symm
  intro ⟨Q, t⟩
  simp only [List.mem_singleton, Prod.mk.injEq, hcross, hQ]

end Mei.FinitePolyhedralComplex
