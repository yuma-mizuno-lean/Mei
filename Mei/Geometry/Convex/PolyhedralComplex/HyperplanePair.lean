/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision
public import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus

/-!
# The complexes cut out by one and by two linear hyperplanes

For a rational continuous linear functional `f`, the complex `hyperplaneComplex f` has every wall
equal to the hyperplane `ker f`; when `f ≠ 0` the hyperplane is a wall
(`mem_hyperplaneComplex_walls_iff`), while for `f = 0` the complex is the ambient cell and has
no walls. The walls have no singular point (`singularSupport_hyperplaneComplex`), since the
hyperplane has empty relative boundary, so the regular locus is the whole space and is a single
convex coefficient chart. A segment between off-wall points crosses no wall when its endpoints
lie on the same side of `ker f` (`crossings_hyperplaneComplex_eq_empty`), and crosses the
hyperplane exactly once when they lie on opposite sides
(`crossings_hyperplaneComplex_eq_singleton`). Adding a second rational functional `g` gives
`hyperplanePairComplex f g`, which subdivides it (`isSubdivision_hyperplanePairComplex`).
Every wall of the pair lies in `ker f` or in `ker g`
(`exists_subset_ker_of_mem_hyperplanePairComplex_walls`). When `f ≠ 0` and `g` does not vanish on
`ker f`, the hyperplane `ker f` is a cell of the first complex but not of the second, so the
two complexes differ (`hyperplaneComplex_ne_hyperplanePairComplex`).

Both complexes are `FinitePolyhedralComplex.ofArrangement` of linear rows, so their cells are
conical.
-/

public section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {f g : V →L[ℝ] ℝ}

/-- The complex of the closures of the sign cells of the single hyperplane `ker f`. For
`f ≠ 0` its cells are the hyperplane and its two closed half-spaces; for `f = 0` it is the
ambient cell alone. -/
noncomputable def hyperplaneComplex (f : V →L[ℝ] ℝ)
    (hf : Toric.IsRationalFunctional h f.toLinearMap) : FinitePolyhedralComplex h :=
  ofArrangement (fun _ : Unit => f.toContinuousAffineMap) (fun _ => hf)

/-- The two defining functionals of a hyperplane pair, indexed by `Bool`: row `false` is `f`
and row `true` is `g`. -/
def hyperplanePairRows (f g : V →L[ℝ] ℝ) : Bool → V →L[ℝ] ℝ := fun j => cond j g f

/-- Row `false` of a hyperplane pair is `f`. -/
@[simp]
theorem hyperplanePairRows_false (f g : V →L[ℝ] ℝ) : hyperplanePairRows f g false = f := (rfl)

/-- Row `true` of a hyperplane pair is `g`. -/
@[simp]
theorem hyperplanePairRows_true (f g : V →L[ℝ] ℝ) : hyperplanePairRows f g true = g := (rfl)

variable (hf : Toric.IsRationalFunctional h f.toLinearMap)
  (hg : Toric.IsRationalFunctional h g.toLinearMap)

include hf hg in
/-- Both rows of a hyperplane pair of rational functionals are rational. -/
theorem isRationalFunctional_hyperplanePairRows (j : Bool) :
    Toric.IsRationalFunctional h (hyperplanePairRows f g j).toLinearMap := by
  cases j
  · exact hf
  · exact hg

/-- The complex of the closures of the sign cells of the two hyperplanes `ker f` and `ker g`.
Its row `false` is `f` and its row `true` is `g`. -/
noncomputable def hyperplanePairComplex (f g : V →L[ℝ] ℝ)
    (hf : Toric.IsRationalFunctional h f.toLinearMap)
    (hg : Toric.IsRationalFunctional h g.toLinearMap) : FinitePolyhedralComplex h :=
  ofArrangement (fun j => (hyperplanePairRows f g j).toContinuousAffineMap)
    (isRationalFunctional_hyperplanePairRows hf hg)

/-- Every cell of the hyperplane complex is conical. -/
theorem isConical_hyperplaneComplex : (hyperplaneComplex f hf).IsConical :=
  isConical_ofArrangement (fun _ : Unit => f) (fun _ => hf)

/-- Every cell of the hyperplane-pair complex is conical. -/
theorem isConical_hyperplanePairComplex : (hyperplanePairComplex f g hf hg).IsConical :=
  isConical_ofArrangement (hyperplanePairRows f g) (isRationalFunctional_hyperplanePairRows hf hg)

/-- Adding a hyperplane subdivides the complex of the first one. -/
theorem isSubdivision_hyperplanePairComplex :
    (hyperplanePairComplex f g hf hg).IsSubdivision (hyperplaneComplex f hf) :=
  ofArrangement_isSubdivision_comp (fun j => (hyperplanePairRows f g j).toContinuousAffineMap)
    (isRationalFunctional_hyperplanePairRows hf hg) (fun _ : Unit => false)

/-- Every wall of the hyperplane complex is the hyperplane `ker f`. -/
theorem eq_ker_of_mem_hyperplaneComplex_walls {P : Set V}
    (hP : P ∈ (hyperplaneComplex f hf).walls) : P = {θ | f θ = 0} := by
  obtain ⟨-, hPZ⟩ := exists_subset_zeroLocus_of_mem_ofArrangement_walls _ _ hP
  obtain ⟨σ, ⟨p, hp⟩, rfl⟩ := mem_ofArrangement_cells.mp
    ((hyperplaneComplex f hf).mem_cells_of_mem_walls hP)
  have hfp : f p = 0 := by simpa using hPZ (subset_closure hp)
  have hσ : σ () = 0 := by
    rw [← mem_signCell.mp hp ()]
    simp [hfp]
  ext θ
  rw [closure_signCell ⟨p, hp⟩]
  simp [mem_weakSignCell, hσ]

/-- The hyperplane `ker f` of a nonzero rational functional is the unique wall of its
complex. -/
theorem mem_hyperplaneComplex_walls_iff (hf0 : f ≠ 0) {P : Set V} :
    P ∈ (hyperplaneComplex f hf).walls ↔ P = {θ | f θ = 0} := by
  refine ⟨eq_ker_of_mem_hyperplaneComplex_walls hf, ?_⟩
  rintro rfl
  have hne : (f.toContinuousAffineMap : V →ᴬ[ℝ] ℝ).toAffineMap.linear ≠ 0 := by
    intro h0
    exact hf0 (ContinuousLinearMap.coe_injective h0)
  obtain ⟨Q, hQ, -, hQZ⟩ := exists_mem_ofArrangement_walls_subset_zeroLocus
    (fun _ : Unit => f.toContinuousAffineMap) (fun _ => hf) (j := ()) hne (x := 0) (by simp)
  obtain rfl := eq_ker_of_mem_hyperplaneComplex_walls hf hQ
  exact hQ

/-- The walls of the hyperplane complex have no singular point: every wall is the hyperplane
`ker f`, which is its own affine span and so has empty relative boundary. -/
@[simp]
theorem singularSupport_hyperplaneComplex :
    singularSupport (fun P : (hyperplaneComplex f hf).walls => (P : Set V)) = ∅ := by
  have hfr : intrinsicFrontier ℝ {θ : V | f θ = 0} = ∅ := by
    have hle : affineSpan ℝ {θ : V | f θ = 0} ≤ (LinearMap.ker f.toLinearMap).toAffineSubspace :=
      affineSpan_le.mpr fun θ hθ => by simpa using hθ
    have hpre : ((↑) : affineSpan ℝ {θ : V | f θ = 0} → V) ⁻¹' {θ | f θ = 0} = univ :=
      eq_univ_of_forall fun y => by simpa using hle y.property
    rw [intrinsicFrontier, hpre, frontier_univ, image_empty]
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  rcases mem_singularSupport.mp hx with ⟨P, hP⟩ | ⟨P, Q, hne, -, -⟩
  · rw [eq_ker_of_mem_hyperplaneComplex_walls hf P.property, hfr] at hP
    exact hP
  · exact hne (by rw [eq_ker_of_mem_hyperplaneComplex_walls hf P.property,
      eq_ker_of_mem_hyperplaneComplex_walls hf Q.property])

/-- The regular locus of the hyperplane complex is the whole space, including the hyperplane. -/
@[simp]
theorem regularLocus_hyperplaneComplex : (hyperplaneComplex f hf).regularLocus = univ := by
  rw [regularLocus, singularSupport_hyperplaneComplex, compl_empty]

/-- The whole regular locus of the hyperplane complex is a convex coefficient chart. -/
theorem top_mem_coefficientCharts_hyperplaneComplex :
    ⊤ ∈ (hyperplaneComplex f hf).coefficientCharts := by
  rw [mem_coefficientCharts, TopologicalSpace.Opens.coe_top, image_univ, Subtype.range_coe,
    regularLocus_hyperplaneComplex]
  exact convex_univ

/-- An off-wall point of the complex of a nonzero functional lies off its hyperplane. -/
theorem apply_val_ne_zero_of_hyperplaneComplex (hf0 : f ≠ 0)
    (x : WallComplement (fun P : (hyperplaneComplex f hf).walls => (P : Set V))) :
    f x.val ≠ 0 :=
  x.notMem ⟨_, (mem_hyperplaneComplex_walls_iff hf hf0).mpr rfl⟩

variable {hf} in
/-- A segment between off-wall points of the hyperplane complex meets a wall at the parameters
in `[0, 1]` where the affine function `f` vanishes along it. -/
theorem mem_crossings_hyperplaneComplex
    (x y : WallComplement (fun P : (hyperplaneComplex f hf).walls => (P : Set V)))
    (P : (hyperplaneComplex f hf).walls) (t : ℝ) :
    (P, t) ∈ WallComplement.crossings x y ↔
      t ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap (f x.val) (f y.val) t = 0 := by
  have hl : f (AffineMap.lineMap x.val y.val t) = AffineMap.lineMap (f x.val) (f y.val) t :=
    f.toLinearMap.toAffineMap.apply_lineMap x.val y.val t
  rw [WallComplement.mem_crossings, eq_ker_of_mem_hyperplaneComplex_walls hf P.property]
  exact and_congr_right fun _ => hl ▸ Iff.rfl

variable {hf} in
/-- A segment whose endpoints lie strictly on the same side of `ker f` crosses no wall. -/
theorem crossings_hyperplaneComplex_eq_empty
    {x y : WallComplement (fun P : (hyperplaneComplex f hf).walls => (P : Set V))}
    (hxy : 0 < f x.val * f y.val) : WallComplement.crossings x y = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun ⟨P, t⟩ hc => ?_
  obtain ⟨ht, he⟩ := (mem_crossings_hyperplaneComplex x y P t).mp hc
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact (mem_Ioi.mp (he ▸ (convex_Ioi (0 : ℝ)).lineMap_mem hx hy ht)).false
  · exact (mem_Iio.mp (he ▸ (convex_Iio (0 : ℝ)).lineMap_mem hx hy ht)).false

/-- A segment whose endpoints lie on opposite sides of `ker f` crosses the hyperplane once, at
the parameter `f x / (f x - f y)`. -/
theorem crossings_hyperplaneComplex_eq_singleton (hf0 : f ≠ 0)
    {x y : WallComplement (fun P : (hyperplaneComplex f hf).walls => (P : Set V))}
    (hxy : f x.val * f y.val < 0) :
    WallComplement.crossings x y =
      {(⟨_, (mem_hyperplaneComplex_walls_iff hf hf0).mpr rfl⟩, f x.val / (f x.val - f y.val))} := by
  have hd : f x.val - f y.val ≠ 0 := fun hd => by
    rw [sub_eq_zero.mp hd] at hxy
    exact (mul_self_nonneg _).not_gt hxy
  ext ⟨P, t⟩
  rw [mem_crossings_hyperplaneComplex, mem_singleton_iff, Prod.mk.injEq,
    AffineMap.lineMap_apply_ring']
  have hP : P = ⟨_, (mem_hyperplaneComplex_walls_iff hf hf0).mpr rfl⟩ :=
    Subtype.ext (eq_ker_of_mem_hyperplaneComplex_walls hf P.property)
  simp only [hP, true_and]
  constructor
  · rintro ⟨-, ht⟩
    field_simp
    linarith
  · rintro rfl
    refine ⟨⟨?_, ?_⟩, by field_simp; ring⟩ <;> rcases lt_or_gt_of_ne hd with hd | hd
    · exact div_nonneg_of_nonpos (by nlinarith) hd.le
    · exact div_nonneg (by nlinarith) hd.le
    · exact (div_le_one_of_neg hd).mpr (by nlinarith)
    · exact (div_le_one hd).mpr (by nlinarith)

/-- Every wall of the hyperplane-pair complex lies in `ker f` or in `ker g`. -/
theorem exists_subset_ker_of_mem_hyperplanePairComplex_walls {P : Set V}
    (hP : P ∈ (hyperplanePairComplex f g hf hg).walls) :
    P ⊆ {θ | f θ = 0} ∨ P ⊆ {θ | g θ = 0} := by
  obtain ⟨j, hj⟩ := exists_subset_zeroLocus_of_mem_ofArrangement_walls _ _ hP
  cases j
  · exact Or.inl (by simpa using hj)
  · exact Or.inr (by simpa using hj)

/-- The hyperplane `ker f` is not a cell of the hyperplane-pair complex when `g` takes
nonzero values on it, since it contains points on both sides of `ker g`. -/
theorem ker_notMem_hyperplanePairComplex_cells {θ₀ : V} (hf₀ : f θ₀ = 0) (hg₀ : g θ₀ ≠ 0) :
    {θ | f θ = 0} ∉ (hyperplanePairComplex f g hf hg).cells := by
  intro hcell
  obtain ⟨σ, hσ, hZ⟩ := mem_ofArrangement_cells.mp hcell
  have hmem (θ : V) (hθ : f θ = 0) : θ ∈ weakSignCell
      (fun j => (hyperplanePairRows f g j).toContinuousAffineMap) σ := by
    rw [← closure_signCell hσ, ← hZ]
    simpa using hθ
  have h₁ := mem_weakSignCell.mp (hmem θ₀ hf₀) true
  have h₂ := mem_weakSignCell.mp (hmem (-θ₀) (by simp [hf₀])) true
  simp only [hyperplanePairRows_true, ContinuousLinearMap.coe_toContinuousAffineMap,
    map_neg] at h₁ h₂
  cases hs : σ true
  · exact hg₀ (h₁.1 hs)
  · exact hg₀ (le_antisymm (h₁.2.1 hs) (by linarith [h₂.2.1 hs]))
  · exact hg₀ (le_antisymm (by linarith [h₂.2.2 hs]) (h₁.2.2 hs))

/-- The complexes cut out by one and by two hyperplanes differ when the second functional
does not vanish on the kernel of the first. -/
theorem hyperplaneComplex_ne_hyperplanePairComplex (hf0 : f ≠ 0) {θ₀ : V} (hf₀ : f θ₀ = 0)
    (hg₀ : g θ₀ ≠ 0) : hyperplaneComplex f hf ≠ hyperplanePairComplex f g hf hg := by
  intro heq
  have hZ : {θ | f θ = 0} ∈ (hyperplaneComplex f hf).walls :=
    (mem_hyperplaneComplex_walls_iff hf hf0).mpr rfl
  rw [heq] at hZ
  exact ker_notMem_hyperplanePairComplex_cells hf hg hf₀ hg₀
    ((hyperplanePairComplex f g hf hg).mem_cells_of_mem_walls hZ)

end Mei.FinitePolyhedralComplex
