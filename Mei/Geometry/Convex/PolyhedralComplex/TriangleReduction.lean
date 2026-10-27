/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.SimultaneousPath
public import Mathlib.Algebra.Group.Subgroup.MulOpposite

/-!
# Reduction of polygonal crossing words to triangles

The word of an admissible polygonal loop lies in the normal closure of words
of admissible three-edge loops. In an open convex region all these loops stay
in that region. A common apex is chosen with admissible spokes to every vertex
of the original polygon; no perturbation of its edges or endpoints is needed.
The filled triangles may meet joints, and may be degenerate. Reducing each
triangle further to small joint meridians is a separate geometric step.

The construction uses `WallComplement.exists_mem_open_admissible_spokes` and
`Quiver.Path.mul_weight_mul_inv_mem_of_isChain`. Mathlib's opposite group keeps
the first crossing rightmost while consecutive spoke factors cancel. The final
conjugation accounts for the original loop's basepoint. No commutativity of
wall generators is assumed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

/-- Words of admissible three-edge loops with vertices in the prescribed set.
For a convex set, their entire filled triangles lie in it. Repeated vertices
and degenerate triangles are included. -/
def triangleWords (ν : C.walls → V →ₗ[ℝ] ℝ) (U : Set V) : Set (FreeGroup C.walls) :=
  {g | ∃ (x y z : WallComplement (fun P : C.walls => (P : Set V)))
    (e : x ⟶ y) (f : y ⟶ z) (r : z ⟶ x),
    x.val ∈ U ∧ y.val ∈ U ∧ z.val ∈ U ∧
      g = ((e.toPath.cons f).cons r).crossingWord ν}

/-- The membership characterization of the triangular relations. -/
@[simp]
theorem mem_triangleWords (ν : C.walls → V →ₗ[ℝ] ℝ) (U : Set V)
    (g : FreeGroup C.walls) :
    g ∈ C.triangleWords ν U ↔
      ∃ (x y z : WallComplement (fun P : C.walls => (P : Set V)))
        (e : x ⟶ y) (f : y ⟶ z) (r : z ⟶ x),
        x.val ∈ U ∧ y.val ∈ U ∧ z.val ∈ U ∧
          g = ((e.toPath.cons f).cons r).crossingWord ν := Iff.rfl

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x : WallComplement (fun P : C.walls => (P : Set V))}

/-- If every admissible triangle from one apex through two vertices of a
polygon has word in a normal subgroup, so does the polygon. The original path
is kept fixed. -/
theorem crossingWord_mem_of_triangles_mem (p : AdmissiblePLPath x x)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (K : Subgroup (FreeGroup C.walls)) (hK : K.Normal)
    (z : WallComplement (fun P : C.walls => (P : Set V)))
    (s : ∀ u (_hu : u ∈ p.vertices), z ⟶ u)
    (htri : ∀ u (hu : u ∈ p.vertices) v (hv : v ∈ p.vertices) (e : u ⟶ v),
      (((s u hu).toPath.cons e).cons (Quiver.reverse (s v hv))).crossingWord ν ∈ K) :
    p.crossingWord ν ∈ K := by
  classical
  let t := fun u => if hu : u ∈ p.vertices then
    C.segmentCrossingWord ν (s u hu) else 1
  let w := fun {u v : WallComplement (fun P : C.walls => (P : Set V))}
    (e : u ⟶ v) => MulOpposite.op (C.segmentCrossingWord ν e)
  have hlocal (u) (hu : u ∈ p.vertices) (v) (hv : v ∈ p.vertices) (e : u ⟶ v) :
      (MulOpposite.op (t u) * w e * (MulOpposite.op (t v))⁻¹) ∈ K.op := by
    have hm := htri u hu v hv e
    simpa only [Subgroup.mem_op, MulOpposite.unop_mul, MulOpposite.unop_inv,
      MulOpposite.unop_op, t, dite_eq_left hu, dite_eq_left hv, w, crossingWord_cons,
      Quiver.Hom.toPath, crossingWord_nil, mul_one,
      C.segmentCrossingWord_reverse ν hν] using hm
  have hchain : p.vertices.IsChain (fun u v => ∀ e : u ⟶ v,
      MulOpposite.op (t u) * w e * (MulOpposite.op (t v))⁻¹ ∈ K.op) := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro u v l₁ l₂ he e
    exact hlocal u (by rw [he]; simp) v (by rw [he]; simp) e
  have hmem := p.mul_weight_mul_inv_mem_of_isChain K.op.toSubmonoid w
    (fun u => MulOpposite.op (t u)) hchain
  have hweight {a b} (q : AdmissiblePLPath a b) :
      MulOpposite.unop (q.weight w) = q.crossingWord ν := by
    induction q with
    | nil => simp
    | cons q e ih => simp only [weight_cons, MulOpposite.unop_mul, w,
        MulOpposite.unop_op, ih, crossingWord_cons]
  have hg : (t x)⁻¹ * p.crossingWord ν * t x ∈ K := by
    simpa only [Subgroup.mem_toSubmonoid, Subgroup.mem_op, MulOpposite.unop_mul,
      MulOpposite.unop_inv, MulOpposite.unop_op, hweight, mul_assoc] using hmem
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel, mul_one] using
    hK.conj_mem _ hg (t x)

/-- An admissible polygonal loop reduces to triangular relations in any open
set containing its vertices. If that set is convex, the triangles and all their
spokes remain in it. This is a reduction to triangles, not to joint meridians. -/
theorem crossingWord_mem_normalClosure_triangles (p : AdmissiblePLPath x x)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    {U : Set V} (hU : IsOpen U) (hp : ∀ u ∈ p.vertices, u.val ∈ U) :
    p.crossingWord ν ∈ Subgroup.normalClosure (C.triangleWords ν U) := by
  classical
  have := h.finiteDimensional
  let A := p.vertices.toFinset
  obtain ⟨z, hzU, hz⟩ := WallComplement.exists_mem_open_admissible_spokes
    (fun P : C.walls => (P : Set V))
    (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
    (fun P => C.finrank_direction_add_one_of_mem_walls P.property)
    (fun u : A => u.val) hU ⟨x.val, hp x p.start_mem_vertices⟩
  have hs (u) (hu : u ∈ p.vertices) : Nonempty (z ⟶ u) :=
    hz ⟨u, by simpa only [A, List.mem_toFinset] using hu⟩
  let s := fun u hu => (hs u hu).some
  exact p.crossingWord_mem_of_triangles_mem ν hν _
    (Subgroup.normalClosure_normal (s := C.triangleWords ν U)) z s
    (fun u hu v hv e => Subgroup.subset_normalClosure
      ⟨z, u, v, s u hu, e, Quiver.reverse (s v hv), hzU, hp u hu, hp v hv, rfl⟩)

end Quiver.Path
