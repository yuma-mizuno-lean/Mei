/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision
public import Mei.Geometry.Toric.Algebraic.DualLattice
public import Mei.Geometry.Convex.Polyhedron.SignCell.Interior
public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.ScatteringDiagram.KS.Space

/-!
# Bounded-degree hyperplane arrangements

The nonzero allowed degrees below a cutoff define a finite conical complex in
the continuous real dual of a lattice. These complexes cover the whole dual
space, subdivide one another as the cutoff increases, and express each retained
degree hyperplane as a union of cells. Each retained nonzero degree hyperplane
is covered by walls, so points off the walls have no vanishing retained degree.
They supply the supports on which finite-order scattering labels can be
assigned by sign factorization.

The construction uses `Mei.FinitePolyhedralComplex.ofArrangement`, the existing
closures of realized sign cells, and the integral dual lattice obtained from
`TauCeti.Toric.IsIntegralLattice.realCharacter`. Cells may have lineality; no
finite generation or saturation of the positive monoid is required.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open Mei.Convex Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)

/-- The finite conical complex cut out by the hyperplanes of nonzero allowed
lattice degrees of order at most `k`, in the continuous real dual. -/
def arrangementComplex (k : ℕ) : FinitePolyhedralComplex h.continuousDual :=
  ofArrangement (fun n : ↥(d.cutoff k \ {0}) =>
    (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap)
    (fun n => h.isRationalFunctional_continuousDual_eval n)

/-- The arrangement complex is the arrangement of the retained evaluation rows. -/
theorem arrangementComplex_eq_ofArrangement (k : ℕ) :
    d.arrangementComplex h k = ofArrangement (fun n : ↥(d.cutoff k \ {0}) =>
      (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap)
      (fun n => h.isRationalFunctional_continuousDual_eval n) := (rfl)

/-- The cells are precisely the closures of the realized degree-sign loci. -/
@[simp]
theorem mem_arrangementComplex_cells (k : ℕ) (P : Set (V →L[ℝ] ℝ)) :
    P ∈ (d.arrangementComplex h k).cells ↔
      ∃ σ : (↥(d.cutoff k \ {0})) → SignType,
        (signCell (fun n : ↥(d.cutoff k \ {0}) =>
          (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap)
          σ).Nonempty ∧
        P = closure (signCell
          (fun n : ↥(d.cutoff k \ {0}) =>
            (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap) σ) := by
  rw [arrangementComplex_eq_ofArrangement]
  exact mem_ofArrangement_cells

/-- Every dual point belongs to the bounded-degree arrangement. -/
@[simp]
theorem support_arrangementComplex (k : ℕ) :
    (d.arrangementComplex h k).support = Set.univ := by
  rw [arrangementComplex_eq_ofArrangement]
  exact support_ofArrangement _ _

/-- Every arrangement cell is a cone with apex zero, allowing lineality. -/
theorem isConical_arrangementComplex (k : ℕ) :
    (d.arrangementComplex h k).IsConical := by
  rw [arrangementComplex_eq_ofArrangement]
  exact isConical_ofArrangement _ _

/-- Increasing the degree cutoff subdivides the previous arrangement without
changing its support. -/
theorem arrangementComplex_isSubdivision {k l : ℕ} (hkl : k ≤ l) :
    (d.arrangementComplex h l).IsSubdivision (d.arrangementComplex h k) := by
  let f : (↥(d.cutoff k \ {0})) → (↥(d.cutoff l \ {0})) :=
    fun n => ⟨n, d.cutoff_mono hkl n.property.1, n.property.2⟩
  rw [arrangementComplex_eq_ofArrangement, arrangementComplex_eq_ofArrangement]
  exact ofArrangement_isSubdivision_comp
    (fun n : ↥(d.cutoff l \ {0}) =>
      (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap)
    (fun n => h.isRationalFunctional_continuousDual_eval n) f

/-- Every retained degree hyperplane is a union of arrangement cells contained
in that hyperplane. For the zero degree, both sides are the whole dual space. -/
theorem hyperplane_eq_iUnion_arrangementComplex_cells {k : ℕ} {n : N}
    (hn : n ∈ d.cutoff k) :
    {θ : V →L[ℝ] ℝ | θ (i n) = 0} =
      ⋃ (P : Set (V →L[ℝ] ℝ)) (_ : P ∈ (d.arrangementComplex h k).cells)
        (_ : P ⊆ {θ | θ (i n) = 0}), P := by
  by_cases hne : n = 0
  · subst hne
    ext θ
    obtain ⟨P, hP, hθP⟩ := mem_support.mp (by simp : θ ∈ (d.arrangementComplex h k).support)
    simp only [map_zero, Set.ofPred_true, Set.mem_univ, Set.subset_univ, Set.mem_iUnion,
      true_iff]
    exact ⟨P, hP, trivial, hθP⟩
  rw [arrangementComplex_eq_ofArrangement]
  exact zeroLocus_eq_iUnion_ofArrangement_cells
    (fun a : ↥(d.cutoff k \ {0}) =>
      (ContinuousLinearMap.apply ℝ ℝ (i a)).toContinuousAffineMap)
    (fun a => h.isRationalFunctional_continuousDual_eval a)
    ⟨n, hn, hne⟩

/-- The intersection of all retained hyperplanes is itself a cell. It need not
be a point when the allowed degrees do not span the lattice. -/
theorem commonKernel_mem_arrangementComplex_cells (k : ℕ) :
    {θ : V →L[ℝ] ℝ | ∀ n ∈ d.cutoff k, θ (i n) = 0} ∈
      (d.arrangementComplex h k).cells := by
  let g := fun n : ↥(d.cutoff k \ {0}) =>
    (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap
  have hzero : (signCell g (fun _ => 0)).Nonempty := by
    refine ⟨0, mem_signCell.mpr ?_⟩
    simp [g]
  apply (d.mem_arrangementComplex_cells h k _).mpr
  refine ⟨fun _ => 0, hzero, ?_⟩
  rw [closure_signCell hzero]
  ext θ
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hθ
    apply mem_weakSignCell.mpr
    intro n
    simp [g, hθ n n.property.1]
  · intro hθ n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · exact (mem_weakSignCell.mp hθ ⟨n, hn, hn0⟩).1 rfl

/-- Every wall of the degree arrangement lies in a hyperplane of a retained
nonzero allowed degree. Redundant hyperplanes and lineality are allowed. -/
theorem exists_degree_forall_eq_zero_of_mem_arrangementComplex_walls
    {k : ℕ} {P : Set (V →L[ℝ] ℝ)} (hP : P ∈ (d.arrangementComplex h k).walls) :
    ∃ n ∈ d.cutoff k \ {0}, ∀ θ ∈ P, θ (i n) = 0 := by
  let := h.continuousDual.finiteDimensional
  have hcell := (d.arrangementComplex h k).mem_cells_of_mem_walls hP
  obtain ⟨σ, hσ, heq⟩ := (d.mem_arrangementComplex_cells h k P).mp hcell
  have hspan : affineSpan ℝ P ≠ ⊤ :=
    (affineSpan ℝ P).ne_top_of_finrank_direction_add_one_eq
      ((d.arrangementComplex h k).finrank_direction_add_one_of_mem_walls hP)
  rw [heq] at hspan
  obtain ⟨n, hn⟩ := exists_zero_sign_of_affineSpan_ne_top hσ hspan
  refine ⟨n, n.property, ?_⟩
  intro θ hθ
  rw [heq, closure_signCell hσ] at hθ
  exact (mem_weakSignCell.mp hθ n).1 hn

/-- Every retained nonzero degree hyperplane is covered by walls of the arrangement:
each of its points lies on a codimension-one cell. -/
theorem exists_mem_arrangementComplex_walls_of_eval_eq_zero {k : ℕ} {n : N}
    (hn : n ∈ d.cutoff k \ {0}) {θ : V →L[ℝ] ℝ} (hθ : θ (i n) = 0) :
    ∃ P ∈ (d.arrangementComplex h k).walls, θ ∈ P := by
  have hnz : (ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap ≠ 0 := by
    intro he
    have hpos : (0 : ℝ) < h.continuousRealCharacter d.degree (i n) := by
      simpa using (Int.cast_pos.mpr
        (d.degree_pos ((d.mem_cutoff).mp hn.1).1 hn.2) : (0 : ℝ) < d.degree n)
    have hv := congrArg (fun f : (V →L[ℝ] ℝ) →ₗ[ℝ] ℝ =>
      f (h.continuousRealCharacter d.degree)) he
    simp only [LinearMap.zero_apply] at hv
    exact hpos.ne' hv
  obtain ⟨P, hP, hθP, _⟩ := exists_mem_ofArrangement_walls_subset_zeroLocus
    (fun n : ↥(d.cutoff k \ {0}) =>
      (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap)
    (fun n => h.isRationalFunctional_continuousDual_eval n) (j := ⟨n, hn⟩) hnz hθ
  rw [arrangementComplex_eq_ofArrangement]
  exact ⟨P, hP, hθP⟩

end Mei.PositiveDegrees

namespace Mei.PositiveDegrees

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : ℤ →+ V} (d : PositiveDegrees ℤ) (h : TauCeti.Toric.IsIntegralLattice i)

/-- In rank one every arrangement wall is the origin, even for nonsaturated
positive monoids and cutoffs before the first nonzero allowed degree. -/
theorem eq_singleton_zero_of_mem_arrangementComplex_walls_int {k : ℕ}
    {P : Set (V →L[ℝ] ℝ)} (hP : P ∈ (d.arrangementComplex h k).walls) : P = {0} := by
  obtain ⟨n, hn, hPn⟩ :=
    d.exists_degree_forall_eq_zero_of_mem_arrangementComplex_walls h hP
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr
    ⟨(d.arrangementComplex h k).nonempty P
      ((d.arrangementComplex h k).mem_cells_of_mem_walls hP), ?_⟩
  intro θ hθ
  apply ((KSSpace.continuousDual h).evaluation_eq_zero_iff_of_int_ne_zero hn.2 θ).mp
  simpa using hPn θ hθ

/-- A rank-one arrangement has exactly one wall as soon as a nonzero allowed
degree survives the cutoff, and no walls before that. -/
@[simp↓]
theorem mem_arrangementComplex_walls_int_iff {k : ℕ} {P : Set (V →L[ℝ] ℝ)} :
    P ∈ (d.arrangementComplex h k).walls ↔
      P = {0} ∧ ∃ n, n ∈ d.cutoff k \ {0} := by
  constructor
  · intro hP
    obtain ⟨n, hn, _⟩ :=
      d.exists_degree_forall_eq_zero_of_mem_arrangementComplex_walls h hP
    exact ⟨d.eq_singleton_zero_of_mem_arrangementComplex_walls_int h hP, n, hn⟩
  · rintro ⟨rfl, n, hn⟩
    obtain ⟨Q, hQ, _⟩ :=
      d.exists_mem_arrangementComplex_walls_of_eval_eq_zero h hn (θ := 0) (by simp)
    rwa [d.eq_singleton_zero_of_mem_arrangementComplex_walls_int h hQ] at hQ

/-- For the standard nonnegative integer grading the wall set is empty at order
zero, and is the singleton consisting of the origin at every positive order. -/
@[simp]
theorem walls_arrangementComplex_nonnegIntegers (k : ℕ) :
    (nonnegIntegers.arrangementComplex h k).walls =
      if k = 0 then ∅ else {{0}} := by
  ext P
  rw [mem_arrangementComplex_walls_int_iff]
  by_cases hk : k = 0
  · simp [hk]
  · have hn : (1 : ℤ) ∈ nonnegIntegers.cutoff k \ {0} := by
      simp only [Set.mem_sdiff, mem_cutoff, mem_nonnegIntegers_monoid,
        nonnegIntegers_degree, Set.mem_singleton_iff]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hex : ∃ n, n ∈ nonnegIntegers.cutoff k \ {0} := ⟨1, hn⟩
    simp only [hex, and_true, ite_eq_right hk, Finset.mem_singleton]

end Mei.PositiveDegrees
