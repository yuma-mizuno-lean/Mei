/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.Path
public import Mei.Geometry.ScatteringDiagram.HyperplanePair

/-!
# The coefficient local system of a single wall

Let `f` be a nonzero rational functional on `V` and let the hyperplane `ker f`, cooriented by
`f`, carry a label `θ` of a group `H` acting on `M` (`FiniteWallDiagram.hyperplaneDiagram`). The
walls of this diagram have no singular point, so its coefficient local system lives on all of
`V`. Its sections need not be constant across the wall: they satisfy the facet equation
`s(Q⁺) = θ⁻¹ • s(Q⁻)` for points `Q⁺` with `0 < f Q⁺` and `Q⁻` with `f Q⁻ < 0`
(`value_eq_inv_smul_value_hyperplaneDiagram`), and more generally the values at the endpoints
of any segment in the domain of a section differ by the crossing factors of
`FiniteWallDiagram.hyperplaneFactor` (`value_hyperplaneDiagram`).

Consequently a family with the same value `c` on both sides of the wall is a section exactly
when `θ • c = c` (`exists_forall_value_eq_iff_smul_eq`); if `θ • c ≠ c`, it is not a section.
For `V = ℝ²` and `f = e₁*` this is the wall `{x = 0}` with normal `e₁*`.

The wall-crossing transport of coefficients follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public section

open CategoryTheory TopologicalSpace Opposite Set Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {f : V →L[ℝ] ℝ}
  {hf : Toric.IsRationalFunctional h f.toLinearMap} {hf0 : f ≠ 0} {H : Type*} [Group H] {θ : H}
  {M : Type*} [MulAction H M]

/-- The values of a section of the coefficient local system of the one-hyperplane diagram at
two off-wall points joined by a segment in its domain differ by the crossing factors of the
endpoints. -/
theorem value_hyperplaneDiagram
    {U : Opens (FinitePolyhedralComplex.hyperplaneComplex f hf).regularSpace}
    (s : ((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem M).presheaf.obj (op U))
    (x y : (FinitePolyhedralComplex.hyperplaneComplex f hf).coefficientPoints)
    (hx : x.val ∈ U) (hy : y.val ∈ U)
    (hseg : segment ℝ x.val.val y.val.val ⊆
      Subtype.val '' (U : Set (FinitePolyhedralComplex.hyperplaneComplex f hf).regularSpace)) :
    ((hyperplaneDiagram hf hf0 θ).coefficientTransport M).value s y hy =
      (hyperplaneFactor f θ y.val.val * (hyperplaneFactor f θ x.val.val)⁻¹) •
        ((hyperplaneDiagram hf hf0 θ).coefficientTransport M).value s x hx := by
  rw [← (hyperplaneDiagram hf hf0 θ).coefficientLocalSystem_segment_of_subset x y hx hy
      ((FinitePolyhedralComplex.hyperplaneComplex f hf).coefficientSegment ⊤
        (FinitePolyhedralComplex.top_mem_coefficientCharts_hyperplaneComplex hf) x y
        (Opens.mem_top _) (Opens.mem_top _)) hseg M s,
    coefficientPathTransport_apply, pathProduct_hyperplaneDiagram]

/-- The facet equation across the wall `ker f`: along a segment in the domain of a section
from `Q⁻` with `f Q⁻ < 0` to `Q⁺` with `0 < f Q⁺`, `s(Q⁺) = θ⁻¹ • s(Q⁻)`. -/
theorem value_eq_inv_smul_value_hyperplaneDiagram
    {U : Opens (FinitePolyhedralComplex.hyperplaneComplex f hf).regularSpace}
    (s : ((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem M).presheaf.obj (op U))
    (x y : (FinitePolyhedralComplex.hyperplaneComplex f hf).coefficientPoints)
    (hx : x.val ∈ U) (hy : y.val ∈ U)
    (hseg : segment ℝ x.val.val y.val.val ⊆
      Subtype.val '' (U : Set (FinitePolyhedralComplex.hyperplaneComplex f hf).regularSpace))
    (hfx : f x.val.val < 0) (hfy : 0 < f y.val.val) :
    ((hyperplaneDiagram hf hf0 θ).coefficientTransport M).value s y hy =
      θ⁻¹ • ((hyperplaneDiagram hf hf0 θ).coefficientTransport M).value s x hx := by
  rw [value_hyperplaneDiagram s x y hx hy hseg]
  simp [hyperplaneFactor_def, hfx.not_gt, hfy]

/-- A point off `ker f`, as an off-wall point of the regular locus of the hyperplane complex. -/
private def offWallPoint (v : V) (hv : f v ≠ 0) :
    (FinitePolyhedralComplex.hyperplaneComplex f hf).coefficientPoints :=
  ⟨⟨v, by simp⟩, fun P hP => hv (by
    rw [FinitePolyhedralComplex.eq_ker_of_mem_hyperplaneComplex_walls hf P.property] at hP
    exact hP)⟩

variable (hf hf0 θ) in
/-- On the one-hyperplane diagram, the family with the same value `c` on both sides of the wall
is a global section of the coefficient local system exactly when the label fixes `c`. Thus for
`θ • c ≠ c` it is not a section. -/
theorem exists_forall_value_eq_iff_smul_eq (c : M) :
    (∃ s : ((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem M).presheaf.obj (op ⊤),
      ∀ x hx, ((hyperplaneDiagram hf hf0 θ).coefficientTransport M).value s x hx = c) ↔
      θ • c = c := by
  have htop := FinitePolyhedralComplex.top_mem_coefficientCharts_hyperplaneComplex hf
  -- a point `v` with `f v = 1`, so that `-v` and `v` lie on opposite sides of the wall
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.mp
    (Module.Dual.range_eq_top_of_ne_zero (f := f.toLinearMap) (by exact_mod_cast hf0)) 1
  replace hv : f v = 1 := hv
  constructor
  · rintro ⟨s, hs⟩
    have he := value_eq_inv_smul_value_hyperplaneDiagram s
      (offWallPoint (-v) (by simp [hv])) (offWallPoint v (by simp [hv]))
      (Opens.mem_top _) (Opens.mem_top _) (by simp) (show f (-v) < 0 by simp [hv])
      (show 0 < f v by simp [hv])
    rw [hs, hs] at he
    exact eq_inv_smul_iff.mp he
  · -- transport `c` from `v`; the label and its inverse fix `c`
    intro hc
    have hc' : θ⁻¹ • c = c := by rw [inv_smul_eq_iff, hc]
    refine ⟨((hyperplaneDiagram hf hf0 θ).coefficientTransport M).parallelSection
      (by simpa using htop) le_rfl (offWallPoint v (by simp [hv])) (Opens.mem_top _) c,
      fun y hy => ?_⟩
    rw [DenseBasisTransport.value_parallelSection,
      (hyperplaneDiagram hf hf0 θ).coefficientTransport_transport M ⊤ htop,
      coefficientPathTransport_apply, pathProduct_hyperplaneDiagram]
    simp only [hyperplaneFactor_def, mul_smul]
    split_ifs <;> simp [hc, hc']

end Mei.FiniteWallDiagram
