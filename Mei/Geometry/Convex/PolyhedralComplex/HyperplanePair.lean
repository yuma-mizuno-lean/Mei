/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision

/-!
# The complexes cut out by one and by two linear hyperplanes

For a rational continuous linear functional `f`, the complex `hyperplaneComplex f` has every wall
equal to the hyperplane `ker f`; when `f ≠ 0` the hyperplane is a wall
(`mem_hyperplaneComplex_walls_iff`), while for `f = 0` the complex is the ambient cell and has
no walls. Adding a second rational functional `g` gives
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

/-- The complex of the closures of the sign cells of the two hyperplanes `ker f` and `ker g`.
Its row `false` is `f` and its row `true` is `g`. -/
noncomputable def hyperplanePairComplex (f g : V →L[ℝ] ℝ)
    (hf : Toric.IsRationalFunctional h f.toLinearMap)
    (hg : Toric.IsRationalFunctional h g.toLinearMap) : FinitePolyhedralComplex h :=
  ofArrangement (fun j : Bool => (cond j g f).toContinuousAffineMap)
    (fun j => by cases j <;> assumption)

variable (hf : Toric.IsRationalFunctional h f.toLinearMap)
  (hg : Toric.IsRationalFunctional h g.toLinearMap)

/-- Every cell of the hyperplane complex is conical. -/
theorem isConical_hyperplaneComplex : (hyperplaneComplex f hf).IsConical :=
  isConical_ofArrangement (fun _ : Unit => f) (fun _ => hf)

/-- Every cell of the hyperplane-pair complex is conical. -/
theorem isConical_hyperplanePairComplex : (hyperplanePairComplex f g hf hg).IsConical :=
  isConical_ofArrangement (fun j : Bool => cond j g f) (fun j => by cases j <;> assumption)

/-- Adding a hyperplane subdivides the complex of the first one. -/
theorem isSubdivision_hyperplanePairComplex :
    (hyperplanePairComplex f g hf hg).IsSubdivision (hyperplaneComplex f hf) :=
  ofArrangement_isSubdivision_comp (fun j : Bool => (cond j g f).toContinuousAffineMap)
    (fun j => by cases j <;> assumption) (fun _ : Unit => false)

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

/-- Every wall of the hyperplane-pair complex lies in `ker f` or in `ker g`. -/
theorem exists_subset_ker_of_mem_hyperplanePairComplex_walls {P : Set V}
    (hP : P ∈ (hyperplanePairComplex f g hf hg).walls) :
    P ⊆ {θ | f θ = 0} ∨ P ⊆ {θ | g θ = 0} := by
  obtain ⟨j, hj⟩ := exists_subset_zeroLocus_of_mem_ofArrangement_walls _ _ hP
  cases j
  · exact Or.inl hj
  · exact Or.inr hj

/-- The hyperplane `ker f` is not a cell of the hyperplane-pair complex when `g` takes
nonzero values on it, since it contains points on both sides of `ker g`. -/
theorem ker_notMem_hyperplanePairComplex_cells {θ₀ : V} (hf₀ : f θ₀ = 0) (hg₀ : g θ₀ ≠ 0) :
    {θ | f θ = 0} ∉ (hyperplanePairComplex f g hf hg).cells := by
  intro hcell
  obtain ⟨σ, hσ, hZ⟩ := mem_ofArrangement_cells.mp hcell
  have hmem (θ : V) (hθ : f θ = 0) : θ ∈ weakSignCell
      (fun j : Bool => (cond j g f).toContinuousAffineMap) σ := by
    rw [← closure_signCell hσ, ← hZ]
    exact hθ
  have h₁ := mem_weakSignCell.mp (hmem θ₀ hf₀) true
  have h₂ := mem_weakSignCell.mp (hmem (-θ₀) (by simp [hf₀])) true
  simp only [Bool.cond_true, ContinuousLinearMap.coe_toContinuousAffineMap, map_neg] at h₁ h₂
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
