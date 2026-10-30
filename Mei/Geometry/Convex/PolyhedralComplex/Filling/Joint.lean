/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Local
public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Reduction
public import Mei.Geometry.Convex.PolyhedralComplex.RegularTransport
public import Mei.Geometry.Convex.PolyhedralComplex.Star

/-!
# Generation of loop words by joint meridians

For a finite polyhedral complex covering its ambient space, the crossing word of every
admissible polygonal loop lies in the normal closure of the words of small loops around the
joints, the cells of codimension two. More precisely, the generators `jointMeridianWords ν U`
are the words of admissible triangular meridians whose filled triangles lie in an open
region `U`, meet the codimension-two skeleton at one relative interior point of a joint, avoid
the relative boundary of that joint and all other joints, and meet only cells containing that
joint. When `U` is convex, every admissible loop in `U` has its word in their normal closure;
with `U` the whole space this is the generation of loop words by joint meridians. Consequently
a group labelling of the walls has endpoint-independent path products exactly when it kills
these meridian words.

Each filled triangle avoiding the codimension-at-least-three skeleton is covered by two kinds
of neighbourhoods. Off the codimension-two skeleton, admissible loops in the regular balls of
`FinitePolyhedralComplex.exists_ball_crossingWord_loop_eq_one` have trivial words. At a
relative interior point of a joint, an isolating ball of
`FinitePolyhedralComplex.exists_isolating_ball` meets only cells containing the joint, and
`Quiver.Path.crossingWord_mem_normalClosure_jointTriangleWords` reduces its loops to meridians.
`FinitePolyhedralComplex.crossingWord_triangle_mem_of_cover` assembles these local relations,
and `Quiver.Path.crossingWord_mem_normalClosure_transverse_triangles` reduces an arbitrary loop
to such triangles.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

variable {C}

/-- In an open region, every point off the codimension-at-least-three skeleton has an
open neighbourhood in which every admissible loop has its word in the normal closure of the
joint meridians in the region. -/
theorem exists_isOpen_crossingWord_mem_normalClosure_jointMeridianWords
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    {U : Set V} (hUo : IsOpen U) {θ : V} (hθU : θ ∈ U)
    (hθ : θ ∉ (C.codimensionAtLeast 3).support) :
    ∃ O : Set V, IsOpen O ∧ θ ∈ O ∧
      ∀ (y : WallComplement (fun P : C.walls => (P : Set V))) (p : AdmissiblePLPath y y),
        (∀ w ∈ p.vertices, w.val ∈ O) →
          p.crossingWord ν ∈ Subgroup.normalClosure (C.jointMeridianWords ν U) := by
  by_cases hθ₂ : θ ∈ (C.codimensionAtLeast 2).support
  · -- At a relative interior point of a joint, use an isolating ball inside the region.
    obtain ⟨J, ⟨hJ, hθJ⟩, -⟩ := C.existsUnique_mem_cellsOfCodimension_of_notMem_succ hθ₂ hθ
    obtain ⟨r, hr, -, -, -, hinc⟩ := C.exists_isolating_ball hJ hθJ
    obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.mp hUo θ hθU
    refine ⟨Metric.ball θ r ∩ Metric.ball θ s, Metric.isOpen_ball.inter Metric.isOpen_ball,
      ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hs⟩, fun y p hp => ?_⟩
    exact Subgroup.normalClosure_mono
      (fun g hg => (C.mem_jointMeridianWords ν U g).mpr
        ⟨J, hJ, C.jointTriangleWords_mono ν J (inter_subset_right.trans hsU) hg⟩)
      (p.crossingWord_mem_normalClosure_jointTriangleWords ν hν hJ
        (Metric.isOpen_ball.inter Metric.isOpen_ball) ((convex_ball θ r).inter (convex_ball θ s))
        ⟨θ, ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hs⟩, intrinsicInterior_subset hθJ⟩
        (fun Q hQ hQU => hinc Q hQ (hQU.mono (inter_subset_inter_left _ inter_subset_left)))
        hp)
  · -- Off the codimension-two skeleton, loop words in a regular ball are trivial.
    obtain ⟨r, hr, hword⟩ := C.exists_ball_crossingWord_loop_eq_one ν hν
      (fun hs => hθ₂ (C.singularSupport_walls_subset_support_codimensionAtLeast hs))
    exact ⟨Metric.ball θ r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      fun y p hp => (hword y p hp).symm ▸ one_mem _⟩

/-- If the filled triangle of an admissible triangular loop lies in an open region and avoids
the codimension-at-least-three skeleton, its word lies in the normal closure of the joint
meridians in the region. No transversality of the triangle is needed. -/
theorem crossingWord_triangle_mem_normalClosure_jointMeridianWords
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    {U : Set V} (hUo : IsOpen U)
    {x y z : WallComplement (fun P : C.walls => (P : Set V))}
    (e : x ⟶ y) (f : y ⟶ z) (r : z ⟶ x)
    (hhull : convexHull ℝ {x.val, y.val, z.val} ⊆ U)
    (havoid : Disjoint (convexHull ℝ {x.val, y.val, z.val}) (C.codimensionAtLeast 3).support) :
    ((e.toPath.cons f).cons r).crossingWord ν ∈
      Subgroup.normalClosure (C.jointMeridianWords ν U) := by
  choose O hO hθO hlocal using fun θ : convexHull ℝ {x.val, y.val, z.val} =>
    exists_isOpen_crossingWord_mem_normalClosure_jointMeridianWords ν hν hUo
      (hhull θ.property) (disjoint_left.mp havoid θ.property)
  exact C.crossingWord_triangle_mem_of_cover ν hν _ e f r O hO
    (fun θ hθ => mem_iUnion.mpr ⟨⟨θ, hθ⟩, hθO _⟩) hlocal

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x : Mei.Convex.WallComplement (fun P : C.walls => (P : Set V))}

/-- **Generation of loop words by joint meridians.** For a complex covering the ambient space,
the crossing word of every admissible polygonal loop in a convex open region lies in the
normal closure of the words of the isolating triangular meridians of joints in that region. -/
theorem crossingWord_mem_normalClosure_jointMeridianWords (p : Mei.Convex.AdmissiblePLPath x x)
    (hC : C.support = Set.univ) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    {U : Set V} (hUo : IsOpen U) (hU : Convex ℝ U) (hp : ∀ u ∈ p.vertices, u.val ∈ U) :
    p.crossingWord ν ∈ Subgroup.normalClosure (C.jointMeridianWords ν U) := by
  refine Subgroup.normalClosure_le_normal (fun g hg => ?_)
    (p.crossingWord_mem_normalClosure_transverse_triangles hC ν hν hUo hp)
  obtain ⟨x, y, z, e, f, r, hx, hy, hz, havoid, -, rfl⟩ :=
    (C.mem_transverseTriangleWords ν U g).mp hg
  exact Mei.FinitePolyhedralComplex.crossingWord_triangle_mem_normalClosure_jointMeridianWords
    ν hν hUo e f r (convexHull_min (by simp [insert_subset_iff, hx, hy, hz]) hU) havoid

end Quiver.Path

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- For a complex covering the ambient space, the joint meridians in a convex open region
normally generate the same subgroup as all triangular relations in the region. -/
theorem normalClosure_jointMeridianWords_eq (C : FinitePolyhedralComplex h)
    (hC : C.support = univ) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    {U : Set V} (hUo : IsOpen U) (hU : Convex ℝ U) :
    Subgroup.normalClosure (C.jointMeridianWords ν U) =
      Subgroup.normalClosure (C.triangleWords ν U) := by
  apply le_antisymm (Subgroup.normalClosure_mono (C.jointMeridianWords_subset_triangleWords ν U))
  apply Subgroup.normalClosure_le_normal
  intro g hg
  obtain ⟨x, y, z, e, f, r, hx, hy, hz, rfl⟩ := (C.mem_triangleWords ν U g).mp hg
  apply Quiver.Path.crossingWord_mem_normalClosure_jointMeridianWords _ hC ν hν hUo hU
  intro u hu
  simp only [Quiver.Path.vertices_cons, Quiver.Path.vertices_toPath,
    List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with (((rfl | rfl) | rfl) | rfl) <;> assumption

end Mei.FinitePolyhedralComplex
