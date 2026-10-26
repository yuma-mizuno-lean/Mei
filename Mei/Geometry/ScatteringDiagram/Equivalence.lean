/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Restriction
public import Mei.Geometry.Convex.PolyhedralComplex.Perturbation

/-!
# Equivalence of finite wall diagrams

Two diagrams are equivalent if their products agree on every polygonal vertex
list admissible for both wall families. The complexes can differ. Equivalence
is transitive even when a test path's vertices lie on walls of the intermediate
diagram: perturb the whole list into general position for all three families,
preserving the crossing words in the two original diagrams.

The argument uses the local stability of crossing words from
`Mei.Geometry.Convex.PolyhedralComplex.Perturbation` and approximation of vertex
lists by admissible paths from `Mei.Geometry.Convex.Polyhedron.Perturbation`.
Restriction deleting identity labels, positive rescaling and simultaneous
reversal of normals and labels give equivalent diagrams. Equivalent diagrams
have the same consistency behavior, by approximating loops while preserving
their closedness.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C C' C'' : FinitePolyhedralComplex h} {H K : Type*} [Group H] [Group K]

/-- Products depend on the ambient vertex list, independently of the proofs
of admissibility and of the endpoint presentations. -/
theorem pathProduct_eq_of_vertices_eq (D : FiniteWallDiagram C H)
    {x y x' y' : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    D.pathProduct p = D.pathProduct q := by
  obtain ⟨ε, hε, hp⟩ := p.exists_pos_crossingWord_eq_of_forall₂_dist_lt D.normal D.ker_normal
  have hnear : List.Forall₂ (fun a b => dist a b < ε)
      (p.vertices.map WallComplement.val) (q.vertices.map WallComplement.val) := by
    rw [hpq]
    exact List.forall₂_same.mpr fun _ _ => by simpa using hε
  simp only [pathProduct_def, hp q hnear]

/-- Agreement on every geometric polygonal path admissible for both diagrams.
The equality of ambient vertex lists includes the endpoints and all segments. -/
def Equivalent (D : FiniteWallDiagram C H) (E : FiniteWallDiagram C' H) : Prop :=
  ∀ ⦃x y : WallComplement (fun P : C.walls => (P : Set V))⦄
    ⦃x' y' : WallComplement (fun P : C'.walls => (P : Set V))⦄
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
    p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
      D.pathProduct p = E.pathProduct q

/-- The common-vertex-list characterization of diagram equivalence. -/
theorem equivalent_def (D : FiniteWallDiagram C H) (E : FiniteWallDiagram C' H) :
    D.Equivalent E ↔
      ∀ ⦃x y : WallComplement (fun P : C.walls => (P : Set V))⦄
        ⦃x' y' : WallComplement (fun P : C'.walls => (P : Set V))⦄
        (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
        p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
          D.pathProduct p = E.pathProduct q := Iff.rfl

/-- Every finite wall diagram is equivalent to itself. -/
@[refl]
theorem Equivalent.refl (D : FiniteWallDiagram C H) : D.Equivalent D := by
  intro x y x' y' p q hpq
  exact D.pathProduct_eq_of_vertices_eq p q hpq

variable {D : FiniteWallDiagram C H} {E : FiniteWallDiagram C' H}
  {F : FiniteWallDiagram C'' H}

/-- Agreement on common paths is symmetric. -/
@[symm]
theorem Equivalent.symm (hDE : D.Equivalent E) : E.Equivalent D := by
  intro x y x' y' p q hpq
  exact (hDE q p hpq.symm).symm

/-- Equivalence is transitive, with no common-admissibility assumption on the
test path for the intermediate diagram. -/
@[trans]
theorem Equivalent.trans (hDE : D.Equivalent E) (hEF : E.Equivalent F) :
    D.Equivalent F := by
  have := h.finiteDimensional
  intro x y x' y' p q hpq
  obtain ⟨ε₁, hε₁, hp⟩ := p.exists_pos_crossingWord_eq_of_forall₂_dist_lt D.normal D.ker_normal
  obtain ⟨ε₂, hε₂, hq⟩ := q.exists_pos_crossingWord_eq_of_forall₂_dist_lt F.normal F.ker_normal
  -- Admissibility for the union is stronger than the three separate conditions.
  let W : C.walls ⊕ (C'.walls ⊕ C''.walls) → Set V :=
    Sum.elim (fun P => (P : Set V))
      (Sum.elim (fun P => (P : Set V)) (fun P => (P : Set V)))
  have hpoly : ∀ a, TauCeti.IsConvexPolyhedron (W a) := by
    rintro (P | P | P)
    · exact C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.2)
    · exact C'.isConvexPolyhedron (C'.mem_cells_of_mem_walls P.2)
    · exact C''.isConvexPolyhedron (C''.mem_cells_of_mem_walls P.2)
  have hdim : ∀ a, Module.finrank ℝ (affineSpan ℝ (W a)).direction + 1 =
      Module.finrank ℝ V := by
    rintro (P | P | P)
    · exact C.finrank_direction_add_one_of_mem_walls P.2
    · exact C'.finrank_direction_add_one_of_mem_walls P.2
    · exact C''.finrank_direction_add_one_of_mem_walls P.2
  obtain ⟨a, b, r, hr⟩ := AdmissiblePLPath.exists_forall₂_dist_lt_free_endpoints
    hpoly hdim (l := p.vertices.map WallComplement.val)
    (by simpa using p.vertices_ne_nil) (lt_min hε₁ hε₂)
  -- Present the projected endpoints in the concrete complements used by the diagrams.
  let r₁ : AdmissiblePLPath
      (⟨a.val, fun P => a.notMem (.inl P)⟩ : WallComplement (fun P : C.walls => (P : Set V)))
      ⟨b.val, fun P => b.notMem (.inl P)⟩ :=
    (WallComplement.restrictPrefunctor W Sum.inl).mapPath r
  let r₂ : AdmissiblePLPath
      (⟨a.val, fun P => a.notMem (.inr (.inl P))⟩ :
        WallComplement (fun P : C'.walls => (P : Set V)))
      ⟨b.val, fun P => b.notMem (.inr (.inl P))⟩ :=
    (WallComplement.restrictPrefunctor W (Sum.inr ∘ Sum.inl)).mapPath r
  let r₃ : AdmissiblePLPath
      (⟨a.val, fun P => a.notMem (.inr (.inr P))⟩ :
        WallComplement (fun P : C''.walls => (P : Set V)))
      ⟨b.val, fun P => b.notMem (.inr (.inr P))⟩ :=
    (WallComplement.restrictPrefunctor W (Sum.inr ∘ Sum.inr)).mapPath r
  have hv₁ : r₁.vertices.map WallComplement.val = r.vertices.map WallComplement.val :=
    WallComplement.vertices_restrictPrefunctor W Sum.inl r
  have hv₂ : r₂.vertices.map WallComplement.val = r.vertices.map WallComplement.val :=
    WallComplement.vertices_restrictPrefunctor W (Sum.inr ∘ Sum.inl) r
  have hv₃ : r₃.vertices.map WallComplement.val = r.vertices.map WallComplement.val :=
    WallComplement.vertices_restrictPrefunctor W (Sum.inr ∘ Sum.inr) r
  have hp' := hp r₁ (by rw [hv₁]; exact hr.imp fun _ _ hab => hab.trans_le (min_le_left _ _))
  have hq' := hq r₃ (by
    rw [← hpq, hv₃]
    exact hr.imp fun _ _ hab => hab.trans_le (min_le_right _ _))
  calc
    D.pathProduct p = D.pathProduct r₁ := by simp only [pathProduct_def, hp']
    _ = E.pathProduct r₂ := hDE r₁ r₂ (hv₁.trans hv₂.symm)
    _ = F.pathProduct r₃ := hEF r₂ r₃ (hv₂.trans hv₃.symm)
    _ = F.pathProduct q := by simp only [pathProduct_def, hq']

/-- Relabelling preserves equivalence. -/
theorem Equivalent.relabel (hDE : D.Equivalent E) (f : H →* K) :
    (D.relabel f).Equivalent (E.relabel f) := by
  intro x y x' y' p q hpq
  simpa only [pathProduct_relabel] using congrArg f (hDE p q hpq)

/-- Consistency is preserved by equivalence, including loops whose basepoint
lies on a wall of the other diagram. -/
theorem Equivalent.consistent (hDE : D.Equivalent E) (hc : D.Consistent) : E.Consistent := by
  have := h.finiteDimensional
  apply E.consistent_iff_loops.mpr
  intro x p
  cases p with
  | nil => simp
  | @cons y _ p e =>
    cases p with
    | nil =>
      -- A one-edge loop is a constant segment and crosses no wall.
      simp [pathProduct_def]
    | @cons z _ p f =>
      let loop := (p.cons f).cons e
      obtain ⟨ε, hε, hp⟩ :=
        loop.exists_pos_crossingWord_eq_of_forall₂_dist_lt E.normal E.ker_normal
      obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp p.vertices_head?
      have hv : loop.vertices.map WallComplement.val =
          x.val :: ((l.map WallComplement.val ++ [y.val]) ++ [x.val]) := by
        simp only [loop, Quiver.Path.vertices_cons, List.concat_eq_append, List.map_append,
          List.map_cons, List.map_nil, hl, List.cons_append]
      let W : C'.walls ⊕ C.walls → Set V :=
        Sum.elim (fun P => (P : Set V)) (fun P => (P : Set V))
      have hpoly : ∀ a, TauCeti.IsConvexPolyhedron (W a) := by
        rintro (P | P)
        · exact C'.isConvexPolyhedron (C'.mem_cells_of_mem_walls P.2)
        · exact C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.2)
      have hdim : ∀ a, Module.finrank ℝ (affineSpan ℝ (W a)).direction + 1 =
          Module.finrank ℝ V := by
        rintro (P | P)
        · exact C'.finrank_direction_add_one_of_mem_walls P.2
        · exact C.finrank_direction_add_one_of_mem_walls P.2
      -- Keep the new basepoint common, and perturb the interior vertices.
      obtain ⟨a, q, hq⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt hpoly hdim x.val
        (l := l.map WallComplement.val ++ [y.val]) hε
      let qE : AdmissiblePLPath
          (⟨a.val, fun P => a.notMem (.inl P)⟩ :
            WallComplement (fun P : C'.walls => (P : Set V)))
          ⟨a.val, fun P => a.notMem (.inl P)⟩ :=
        (WallComplement.restrictPrefunctor W Sum.inl).mapPath q
      let qD : AdmissiblePLPath
          (⟨a.val, fun P => a.notMem (.inr P)⟩ :
            WallComplement (fun P : C.walls => (P : Set V)))
          ⟨a.val, fun P => a.notMem (.inr P)⟩ :=
        (WallComplement.restrictPrefunctor W Sum.inr).mapPath q
      have hvE : qE.vertices.map WallComplement.val = q.vertices.map WallComplement.val :=
        WallComplement.vertices_restrictPrefunctor W Sum.inl q
      have hvD : qD.vertices.map WallComplement.val = q.vertices.map WallComplement.val :=
        WallComplement.vertices_restrictPrefunctor W Sum.inr q
      have hw := hp qE (by rwa [hv, hvE])
      calc
        E.pathProduct loop = E.pathProduct qE := by simp only [pathProduct_def, hw]
        _ = D.pathProduct qD := (hDE qD qE (hvD.trans hvE.symm)).symm
        _ = 1 := (D.consistent_iff_loops.mp hc) _ qD

/-- Equivalent diagrams have the same consistency behavior. -/
theorem Equivalent.consistent_iff (hDE : D.Equivalent E) : D.Consistent ↔ E.Consistent :=
  ⟨hDE.consistent, hDE.symm.consistent⟩

/-- Injective homomorphisms of labels reflect equivalence. -/
theorem equivalent_relabel_iff (D : FiniteWallDiagram C H) (E : FiniteWallDiagram C' H)
    (f : H →* K) (hf : Function.Injective f) :
    (D.relabel f).Equivalent (E.relabel f) ↔ D.Equivalent E := by
  constructor
  · intro hDE x y x' y' p q hpq
    apply hf
    simpa only [pathProduct_relabel] using hDE p q hpq
  · exact fun hDE => hDE.relabel f

/-- Changing positive scales of coorientations gives an equivalent diagram. -/
theorem equivalent_rescale (D : FiniteWallDiagram C H) (r : C.walls → ℝ)
    (hr : ∀ P, 0 < r P) : D.Equivalent (D.rescale r hr) := by
  intro x y x' y' p q hpq
  simpa only [pathProduct_rescale] using D.pathProduct_eq_of_vertices_eq p q hpq

/-- Reversing coorientations and labels together gives an equivalent diagram. -/
theorem equivalent_reorient (D : FiniteWallDiagram C H) (s : C.walls → Bool) :
    D.Equivalent (D.reorient s) := by
  intro x y x' y' p q hpq
  simpa only [pathProduct_reorient] using D.pathProduct_eq_of_vertices_eq p q hpq

/-- Deleting identity-labelled walls gives an equivalent diagram, in particular
when restricting to a subcomplex containing every nonidentity wall. -/
theorem equivalent_restrict (D : FiniteWallDiagram C H) (hW : C'.walls ⊆ C.walls)
    (hlabel : ∀ P : C.walls, P.val ∉ C'.walls → D.label P = 1) :
    D.Equivalent (D.restrict hW) := by
  intro x y x' y' p q hpq
  let r := (WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
    (fun P : C'.walls => (⟨P.val, hW P.property⟩ : C.walls))).mapPath p
  have hr : r.vertices.map WallComplement.val = p.vertices.map WallComplement.val :=
    WallComplement.vertices_restrictPrefunctor _ _ p
  calc
    D.pathProduct p = (D.restrict hW).pathProduct r :=
      (D.pathProduct_restrict hW hlabel p).symm
    _ = (D.restrict hW).pathProduct q :=
      (D.restrict hW).pathProduct_eq_of_vertices_eq r q (hr.trans hpq)

end Mei.FiniteWallDiagram
