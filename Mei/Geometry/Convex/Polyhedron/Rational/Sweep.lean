/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Analysis.Convex.Polyhedron.Projection

/-!
# Rational-normal polyhedral sweeps

Fourier–Motzkin elimination gives an actual rational-normal presentation of the
negative-ray sweep. The parameter coefficient of each inequality is its normal
evaluated at the lattice sweeping vector, hence is rational. Every resultant
normal is therefore a rational combination of the original normals.

No transversality assumption is needed. Arbitrary real offsets remain allowed;
when the original offsets are rational, the resulting offsets are rational too.
-/

public section

namespace Mei.Convex

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Rational parameter coefficients preserve rational normals in every
Fourier–Motzkin resultant row. -/
theorem rational_linear_nonnegElimFamily (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Mei.Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (a : ι → ℝ) (ha : ∀ j, ∃ q : ℚ, a j = (q : ℝ)) (k : NonnegElimIndex a) :
    Mei.Toric.IsRationalFunctional h (nonnegElimFamily g a k).toAffineMap.linear := by
  rcases k with j | ⟨j, k⟩
  · rw [nonnegElimFamily_single_linear]
    exact hg j.val
  · rw [nonnegElimFamily_pair_linear]
    exact ((hg j.val).smul (ha k.val)).sub ((hg k.val).smul (ha j.val))

/-- Rational coefficients and rational offsets give rational offsets for each
resultant row. -/
theorem rational_offset_nonnegElimFamily (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, ∃ q : ℚ, g j 0 = (q : ℝ)) (a : ι → ℝ)
    (ha : ∀ j, ∃ q : ℚ, a j = (q : ℝ)) (k : NonnegElimIndex a) :
    ∃ q : ℚ, nonnegElimFamily g a k 0 = (q : ℝ) := by
  rcases k with j | ⟨j, k⟩
  · rw [nonnegElimFamily_single_apply]
    exact hg j.val
  · obtain ⟨aj, haj⟩ := ha j.val
    obtain ⟨ak, hak⟩ := ha k.val
    obtain ⟨bj, hbj⟩ := hg j.val
    obtain ⟨bk, hbk⟩ := hg k.val
    refine ⟨ak * bj - aj * bk, ?_⟩
    rw [nonnegElimFamily_pair_apply, haj, hak, hbj, hbk]
    simp only [Rat.cast_sub, Rat.cast_mul]

end Mei.Convex

namespace Mei.RationalAffinePolyhedron

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The negative-ray sweep of a rational-normal affine presentation along a
lattice vector, with the explicit finite Fourier–Motzkin resultant inequalities. -/
noncomputable def sweep (P : RationalAffinePolyhedron h) (n : N) :
    RationalAffinePolyhedron h :=
  ofFinite
    (Mei.Convex.nonnegElimFamily P.inequality (fun j => (P.inequality j).linear (i n)))
    (Mei.Convex.rational_linear_nonnegElimFamily P.inequality P.rational_linear
      (fun j => (P.inequality j).linear (i n))
      (fun j => (P.rational_linear j).exists_rat_apply n))

/-- The resultant presentation has exactly the original negative-ray sweep as
its carrier, including for tangent sweeping vectors. -/
@[simp]
theorem carrier_sweep (P : RationalAffinePolyhedron h) (n : N) :
    (P.sweep n).carrier = {y : V | ∃ t : ℝ, 0 ≤ t ∧ y + t • i n ∈ P.carrier} := by
  ext y
  unfold sweep
  rw [mem_carrier_ofFinite]
  symm
  simp only [mem_carrier]
  have he := Mei.Convex.setOf_exists_nonneg_add_smul_forall_le_eq P.inequality (i n)
  exact Set.ext_iff.mp he y

/-- Sweeping preserves rational offsets because its resultant coefficients are
rational evaluations of the original normals on a lattice vector. -/
theorem HasRationalOffsets.sweep {P : RationalAffinePolyhedron h}
    (hP : P.HasRationalOffsets) (n : N) : (P.sweep n).HasRationalOffsets := by
  rw [Mei.RationalAffinePolyhedron.sweep]
  rw [hasRationalOffsets_iff] at hP
  apply hasRationalOffsets_ofFinite
  exact Mei.Convex.rational_offset_nonnegElimFamily P.inequality hP
    (fun j => (P.inequality j).linear (i n))
    (fun j => (P.rational_linear j).exists_rat_apply n)

end Mei.RationalAffinePolyhedron

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V}

/-- The property of admitting a rational-normal presentation is preserved by
negative-ray addition in every lattice direction. -/
theorem IsRationalNormalPolyhedron.negRay (hP : IsRationalNormalPolyhedron h P) (n : N) :
    IsRationalNormalPolyhedron h {y : V | ∃ t : ℝ, 0 ≤ t ∧ y + t • i n ∈ P} := by
  rw [isRationalNormalPolyhedron_iff] at hP ⊢
  obtain ⟨Q, rfl⟩ := hP
  exact ⟨Q.sweep n, Q.carrier_sweep n⟩

/-- Negative-ray addition preserves polyhedra that admit rational normals and
rational offsets. -/
theorem IsRationalPolyhedron.negRay (hP : IsRationalPolyhedron h P) (n : N) :
    IsRationalPolyhedron h {y : V | ∃ t : ℝ, 0 ≤ t ∧ y + t • i n ∈ P} := by
  rw [isRationalPolyhedron_iff] at hP ⊢
  obtain ⟨Q, rfl, hQ⟩ := hP
  exact ⟨Q.sweep n, Q.carrier_sweep n, hQ.sweep n⟩

end Mei
