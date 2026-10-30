/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Equivalence
public import Mei.Geometry.Convex.PolyhedralComplex.LocalCrossing

/-!
# Recovering local labels from diagram equivalence

Equivalent finite wall diagrams have the same label at a common regular wall
point when their coorientations agree on a transverse direction. If one diagram
has no wall through the point, the other diagram's local label is the identity.
Neither diagram is required to be consistent. These comparisons allow local
labels to be tracked when a subdivision introduces or deletes walls.

The short-segment argument uses
`FinitePolyhedralComplex.eventually_exists_orderedCrossings_eq_singleton` and
`FiniteWallDiagram.pathProduct_toPath`, as in the local label recovery of
`CompletedDiagram.label_eq_signFactorizationEquiv_symm_zero`. It is the regular
wall-germ test for equivalence in Bridgeland, *Scattering diagrams, Hall algebras
and stability conditions*, §2 (arXiv:1603.00416v4).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V H : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Group H]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C C' : FinitePolyhedralComplex h}

/-- Every sufficiently short segment through a regular wall point, from the
positive side to the negative side, has product equal to the wall label. -/
theorem eventually_exists_pathProduct_eq_label (D : FiniteWallDiagram C H)
    (P : C.walls) {θ v : V} (hθP : θ ∈ (P : Set V))
    (hθ : θ ∉ singularSupport (fun Q : C.walls => (Q : Set V)))
    (hv : 0 < D.normal P v) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (fun Q : C.walls => (Q : Set V))) (e : x ⟶ y),
        x.val = θ + a • v ∧ y.val = θ - a • v ∧
        D.pathProduct e.toPath = D.label P := by
  have htrans : v ∉ (affineSpan ℝ (P : Set V)).direction := by
    rw [← D.ker_normal, LinearMap.mem_ker]
    exact hv.ne'
  filter_upwards [C.eventually_exists_orderedCrossings_eq_singleton hθP hθ htrans,
    self_mem_nhdsWithin] with a ha ha0
  have ha0 : 0 < a := ha0
  obtain ⟨x, y, e, hx, hy, he⟩ := ha
  refine ⟨x, y, e, hx, hy, ?_⟩
  have hd : y.val - x.val = (-2 * a) • v := by rw [hx, hy]; module
  have hneg : D.normal P (y.val - x.val) < 0 := by
    rw [hd, map_smul]
    exact mul_neg_of_neg_of_pos (by linarith) hv
  rw [pathProduct_toPath, he]
  simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton,
    ite_eq_right hneg.not_gt]

/-- Cooriented labels at a common regular wall point agree in equivalent
presentations, even when the ambient complexes differ. -/
theorem Equivalent.label_eq {D : FiniteWallDiagram C H} {E : FiniteWallDiagram C' H}
    (hDE : D.Equivalent E) (P : C.walls) (Q : C'.walls) {θ v : V}
    (hθP : θ ∈ (P : Set V)) (hθQ : θ ∈ (Q : Set V))
    (hθD : θ ∉ singularSupport (fun S : C.walls => (S : Set V)))
    (hθE : θ ∉ singularSupport (fun S : C'.walls => (S : Set V)))
    (hvD : 0 < D.normal P v) (hvE : 0 < E.normal Q v) : D.label P = E.label Q := by
  obtain ⟨a, haD, haE⟩ := ((D.eventually_exists_pathProduct_eq_label P hθP hθD hvD).and
    (E.eventually_exists_pathProduct_eq_label Q hθQ hθE hvE)).exists
  obtain ⟨x, y, e, hx, hy, he⟩ := haD
  obtain ⟨x', y', e', hx', hy', he'⟩ := haE
  have hprod := (equivalent_def D E).mp hDE e.toPath e'.toPath (by
    simp only [Quiver.Path.vertices_toPath, List.map_cons, List.map_nil, hx, hy, hx', hy'])
  exact he.symm.trans (hprod.trans he')

/-- A wall at a regular point has identity label if an equivalent diagram has
no wall through that point. -/
theorem Equivalent.label_eq_one {D : FiniteWallDiagram C H} {E : FiniteWallDiagram C' H}
    (hDE : D.Equivalent E) (P : C.walls) {θ : V}
    (hθP : θ ∈ (P : Set V))
    (hθD : θ ∉ singularSupport (fun S : C.walls => (S : Set V)))
    (hθE : ∀ Q : C'.walls, θ ∉ (Q : Set V)) : D.label P = 1 := by
  classical
  let := h.finiteDimensional
  obtain ⟨v, hv⟩ := LinearMap.surjective (D.normal_ne_zero P) (1 : ℝ)
  have hpos : 0 < D.normal P v := by rw [hv]; norm_num
  have hreg : θ ∉ singularSupport (fun Q : C'.walls => (Q : Set V)) := by
    intro hs
    obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp (singularSupport_subset_iUnion _
      (fun Q => (C'.isConvexPolyhedron (C'.mem_cells_of_mem_walls Q.property)).isClosed) hs)
    exact hθE Q hQ
  have hshort := WallComplement.eventually_exists_crossings_iff
    (fun Q : C'.walls =>
      (C'.isConvexPolyhedron (C'.mem_cells_of_mem_walls Q.property)).isClosed)
    (v := -v) hreg (fun Q hQ => (hθE Q hQ).elim)
  obtain ⟨a, haD, haE⟩ := ((D.eventually_exists_pathProduct_eq_label P hθP hθD hpos).and
    hshort).exists
  obtain ⟨x, y, e, hx, hy, he⟩ := haD
  obtain ⟨x', y', e', hx', hy', hcross⟩ := haE
  have hnil : C'.orderedCrossings e' = [] := by
    symm
    apply (C'.orderedCrossings_eq_iff e' []).mpr
    refine ⟨by simp, ?_⟩
    intro b
    simp only [List.not_mem_nil, false_iff, hcross]
    exact fun hb => hθE b.1 hb.1
  have hprod := (equivalent_def D E).mp hDE e.toPath e'.toPath (by
    simp [Quiver.Path.vertices_toPath, hx, hy, hx', hy', sub_eq_add_neg])
  rw [he, E.pathProduct_toPath, hnil] at hprod
  simpa using hprod

end Mei.FiniteWallDiagram
