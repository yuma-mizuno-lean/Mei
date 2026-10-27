/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Incidence
public import Mei.Geometry.Convex.PolyhedralComplex.Chamber

/-!
# The chambers on the two sides of a cooriented wall

A wall's coorientation determines its incident chambers independently of both the
relative interior point and the positive transverse velocity used to cross it.
The same pair works throughout the wall interior; reversing the velocity exchanges
the two chambers. This makes chamber-indexed data, such as transport potentials,
well defined on oriented wall cells.

The construction uses `FinitePolyhedralComplex.existsUnique_cell_of_transverse_ray`
for one crossing, then `Convex.eventually_add_smul_mem_interior_of_ker_le` to extend
its chamber to all positive transverse crossings. The pair's distinctness and intersection
come from `FinitePolyhedralComplex.exists_transverse_wall_chambers`.
Ordinary interiors are the actual
chambers by `FinitePolyhedralComplex.connectedComponentIn_compl_support_codimensionAtLeast_one`.
Only a neighborhood of one relative interior point must be covered by the complex.
Unbounded cells, lineality and arbitrary real offsets are allowed.
-/

public section

open Set Filter Topology

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A coorientation determines a unique full cell entered by every positive
transverse ray from every relative interior point of the wall. Coverage of a
neighborhood of just one such point suffices. -/
theorem existsUnique_cell_of_positive_transverse_rays (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : ν.ker = (affineSpan ℝ P).direction)
    (hcover : ∃ q ∈ intrinsicInterior ℝ P, q ∈ interior C.support) :
    ∃! Q : Set V, Q ∈ C.cellsOfCodimension 0 ∧ P ⊆ Q ∧
      ∀ q ∈ intrinsicInterior ℝ P, ∀ v : V, 0 < ν v →
        ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ interior Q := by
  have := h.finiteDimensional
  -- Choose one positive crossing to find a chamber with an interior point on that side.
  obtain ⟨q₀, hq₀, hcover⟩ := hcover
  have hne : ν ≠ 0 := by
    intro he
    have hd := C.finrank_direction_add_one_of_mem_walls hP
    rw [← hν, he, LinearMap.ker_zero, finrank_top] at hd
    omega
  obtain ⟨v₀, hv₀⟩ := LinearMap.surjective hne 1
  have hvpos : 0 < ν v₀ := by rw [hv₀]; exact zero_lt_one
  have hvtrans : v₀ ∉ (affineSpan ℝ P).direction := by
    rw [← hν, LinearMap.mem_ker, hv₀]
    exact one_ne_zero
  obtain ⟨Q, ⟨hQ, hPQ, ε, hε, hshort⟩, -⟩ :=
    C.existsUnique_cell_of_transverse_ray hP hq₀ hcover hvtrans
  have hIQ : intrinsicInterior ℝ Q = interior Q :=
    Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
      (C.affineSpan_eq_top_of_mem_cellsOfCodimension_zero hQ)
  have hx : q₀ + (ε / 2) • v₀ ∈ interior Q := by
    rw [← hIQ]
    exact hshort _ ⟨by positivity, by linarith⟩
  -- Tangent motion within the wall transfers that chamber to every positive crossing.
  have hall : ∀ q ∈ intrinsicInterior ℝ P, ∀ v : V, 0 < ν v →
      ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ interior Q := by
    intro q hq v hv
    have hdiff : ν (q - q₀) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hν]
      exact (affineSpan ℝ P).vsub_mem_direction
        (subset_affineSpan ℝ P (intrinsicInterior_subset hq))
        (subset_affineSpan ℝ P (intrinsicInterior_subset hq₀))
    have hxpos : 0 < ν (q₀ + (ε / 2) • v₀ - q) := by
      simp only [map_sub] at hdiff
      simp only [map_sub, map_add, map_smul, smul_eq_mul, hv₀]
      linarith
    exact (C.isConvexPolyhedron ((C.mem_cellsOfCodimension 0 Q).mp hQ).1).convex
      |>.eventually_add_smul_mem_interior_of_ker_le hPQ ν hν.le hq hx hxpos hv
  refine ⟨Q, ⟨hQ, hPQ, hall⟩, ?_⟩
  rintro Q' ⟨hQ', _, hall'⟩
  obtain ⟨t, ht, ht'⟩ := ((hall' q₀ hq₀ v₀ hvpos).and (hall q₀ hq₀ v₀ hvpos)).exists
  exact C.eq_of_mem_intrinsicInterior
    ((C.mem_cellsOfCodimension 0 Q').mp hQ').1
    ((C.mem_cellsOfCodimension 0 Q).mp hQ).1
    (interior_subset_intrinsicInterior ht) (interior_subset_intrinsicInterior ht')

/-- One pair of distinct chambers works for all positive transverse crossings of
an entire cooriented wall interior. Their intersection is exactly the wall.
Negating the coorientation exchanges the roles of the pair. -/
theorem exists_cooriented_wall_chambers (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : ν.ker = (affineSpan ℝ P).direction)
    (hcover : ∃ q ∈ intrinsicInterior ℝ P, q ∈ interior C.support) :
    ∃ Qminus ∈ C.cellsOfCodimension 0, ∃ Qplus ∈ C.cellsOfCodimension 0,
      Qminus ≠ Qplus ∧ Qminus ∩ Qplus = P ∧
      ∀ q ∈ intrinsicInterior ℝ P, ∀ v : V, 0 < ν v →
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          q - t • v ∈ interior Qminus ∧ q + t • v ∈ interior Qplus := by
  obtain ⟨Qplus, ⟨hp, _, hplus⟩, -⟩ :=
    C.existsUnique_cell_of_positive_transverse_rays hP ν hν hcover
  obtain ⟨Qminus, ⟨hm, _, hminus⟩, -⟩ :=
    C.existsUnique_cell_of_positive_transverse_rays hP (-ν) (by simpa using hν) hcover
  have hall : ∀ q ∈ intrinsicInterior ℝ P, ∀ v : V, 0 < ν v →
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        q - t • v ∈ interior Qminus ∧ q + t • v ∈ interior Qplus := by
    intro q hq v hv
    simpa only [LinearMap.neg_apply, map_neg, neg_neg, smul_neg, sub_eq_add_neg] using
      (hminus q hq (-v) (by simpa using hv)).and (hplus q hq v hv)
  -- Identify the simultaneous pair with the pair at one covered transverse crossing.
  obtain ⟨q, hq, hcover⟩ := hcover
  have hνne : ν ≠ 0 := by
    intro hz
    have hd := C.finrank_direction_add_one_of_mem_walls hP
    rw [← hν, hz, LinearMap.ker_zero, finrank_top] at hd
    omega
  obtain ⟨v, hv⟩ := LinearMap.surjective hνne 1
  have hvtrans : v ∉ (affineSpan ℝ P).direction := by
    rw [← hν, LinearMap.mem_ker, hv]
    exact one_ne_zero
  obtain ⟨Rminus, hRm, Rplus, hRp, hne, hinter, ε, hε, hshort⟩ :=
    C.exists_transverse_wall_chambers hP hq hcover hvtrans
  obtain ⟨t, ht, htε⟩ :=
    ((hall q hq v (by rw [hv]; exact zero_lt_one)).and (Ioo_mem_nhdsGT hε)).exists
  have heqm : Rminus = Qminus := C.eq_of_mem_intrinsicInterior
    ((C.mem_cellsOfCodimension 0 Rminus).mp hRm).1
    ((C.mem_cellsOfCodimension 0 Qminus).mp hm).1
    (hshort t htε).1 (interior_subset_intrinsicInterior ht.1)
  have heqp : Rplus = Qplus := C.eq_of_mem_intrinsicInterior
    ((C.mem_cellsOfCodimension 0 Rplus).mp hRp).1
    ((C.mem_cellsOfCodimension 0 Qplus).mp hp).1
    (hshort t htε).2 (interior_subset_intrinsicInterior ht.2)
  subst Rminus Rplus
  exact ⟨Qminus, hm, Qplus, hp, hne, hinter, hall⟩

end Mei.FinitePolyhedralComplex
