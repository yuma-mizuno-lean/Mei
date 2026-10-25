/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision
public import Mei.Geometry.Toric.Algebraic.DualLattice

/-!
# Bounded-degree hyperplane arrangements

The nonzero allowed degrees below a cutoff define a finite conical complex in
the continuous real dual of a lattice. These complexes cover the whole dual
space, subdivide one another as the cutoff increases, and express each retained
degree hyperplane as a union of cells. They supply the supports on which
finite-order scattering labels can be assigned by sign factorization.

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

private instance finiteNonzeroCutoff (k : ℕ) : Finite (↥(d.cutoff k \ {0})) :=
  ((d.finite_cutoff k).sdiff).to_subtype

/-- The finite conical complex cut out by the hyperplanes of nonzero allowed
lattice degrees of order at most `k`, in the continuous real dual. -/
def arrangementComplex (k : ℕ) : FinitePolyhedralComplex h.continuousDual :=
  ofArrangement (fun n : ↥(d.cutoff k \ {0}) =>
    (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap)
    (fun n => h.isRationalFunctional_eval n)

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
  exact mem_ofArrangement_cells

/-- Every dual point belongs to the bounded-degree arrangement. -/
@[simp]
theorem support_arrangementComplex (k : ℕ) :
    (d.arrangementComplex h k).support = Set.univ :=
  support_ofArrangement _ _

/-- Every arrangement cell is a cone with apex zero, allowing lineality. -/
theorem isConical_arrangementComplex (k : ℕ) :
    (d.arrangementComplex h k).IsConical :=
  isConical_ofArrangement _ _

/-- Increasing the degree cutoff subdivides the previous arrangement without
changing its support. -/
theorem arrangementComplex_isSubdivision {k l : ℕ} (hkl : k ≤ l) :
    (d.arrangementComplex h l).IsSubdivision (d.arrangementComplex h k) := by
  let f : (↥(d.cutoff k \ {0})) → (↥(d.cutoff l \ {0})) :=
    fun n => ⟨n, d.cutoff_mono hkl n.property.1, n.property.2⟩
  exact ofArrangement_isSubdivision_comp
    (fun n : ↥(d.cutoff l \ {0}) =>
      (ContinuousLinearMap.apply ℝ ℝ (i n)).toContinuousAffineMap)
    (fun n => h.isRationalFunctional_eval n) f

/-- Every retained degree hyperplane is a union of arrangement cells contained
in that hyperplane. -/
theorem hyperplane_eq_iUnion_arrangementComplex_cells {k : ℕ} {n : N}
    (hn : n ∈ d.cutoff k) (hne : n ≠ 0) :
    {θ : V →L[ℝ] ℝ | θ (i n) = 0} =
      ⋃ (P : Set (V →L[ℝ] ℝ)) (_ : P ∈ (d.arrangementComplex h k).cells)
        (_ : P ⊆ {θ | θ (i n) = 0}), P := by
  exact zeroLocus_eq_iUnion_ofArrangement_cells
    (fun a : ↥(d.cutoff k \ {0}) =>
      (ContinuousLinearMap.apply ℝ ℝ (i a)).toContinuousAffineMap)
    (fun a => h.isRationalFunctional_eval a)
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

end Mei.PositiveDegrees
