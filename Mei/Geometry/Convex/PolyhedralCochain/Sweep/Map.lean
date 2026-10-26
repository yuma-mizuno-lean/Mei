/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Subdivision
public import Mei.Geometry.Convex.PolyhedralCochain.Transverse

/-!
# Sweeping transverse polyhedral cochains

Negative-ray sweeping defines a linear map from cochains transverse to a lattice
vector to cochains of one lower codimension. It is independent of the finite
presentation: orientation reversal negates the sweep, and the swept pieces of
an oriented subdivision subdivide the swept cell. Coefficient maps commute with
this operation.

The construction descends `OrientedCell.sweep` using `PolyhedralCochain.lift` and
`mk_sweep_eq_sum_of_isOrientedSubdivision`. Its domain is the existing
`transverseSubmodule`, so transversality concerns the cochain rather than a
chosen representative. This is the sweep used to turn transverse obstruction
cochains into wall corrections; the coboundary homotopy identity is not proved here.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

open Classical in
private def sweepExtension (n : N) :
    PolyhedralCochain R h E (k + 1) →ₗ[R] PolyhedralCochain R h E k :=
  lift (fun σ => if hn : i n ∉ (affineSpan ℝ σ.carrier).direction
      then mk (σ.sweep n hn) else 0)
    (fun σ => by
      by_cases hn : i n ∈ (affineSpan ℝ σ.carrier).direction <;>
        ext c <;> simp [hn])
    (fun σ Q hQ => by
      by_cases hn : i n ∈ (affineSpan ℝ σ.carrier).direction
      · simp only [dite_eq_right (not_not.mpr hn)]
        exact (Finset.sum_eq_zero fun τ hτ =>
          dite_eq_right (not_not.mpr (hQ.direction_eq hτ ▸ hn))).symm
      · rw [dite_eq_left hn]
        ext c
        rw [LinearMap.sum_apply, mk_sweep_eq_sum_of_isOrientedSubdivision hQ n hn c]
        rw [← Finset.sum_attach Q]
        apply Finset.sum_congr rfl
        intro τ _
        simp only [dite_eq_left (fun hm => hn (hQ.direction_eq τ.property ▸ hm))])

open Classical in
private theorem sweepExtension_mk (n : N) (σ : OrientedCell h (k + 1)) (c : E) :
    sweepExtension n (mk (R := R) σ c) =
      if hn : i n ∉ (affineSpan ℝ σ.carrier).direction then mk (σ.sweep n hn) c else 0 := by
  simp only [sweepExtension, lift_mk]
  split_ifs <;> rfl

/-- The negative-ray sweep on transverse cochains. The support of each generator
is swept in direction `-i n`, and its conormal orientation is contracted by `i n`. -/
def sweep (n : N) :
    transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n) →ₗ[R]
      PolyhedralCochain R h E k :=
  (sweepExtension n).domRestrict (transverseSubmodule (i n))

/-- Sweeping a transverse generator gives its oriented-cell sweep. -/
@[simp]
theorem sweep_mk (n : N) (σ : OrientedCell h (k + 1))
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) (c : E) :
    sweep n ⟨mk (R := R) σ c, mk_mem_transverseSubmodule (i n) σ hn c⟩ =
      mk (σ.sweep n hn) c := by
  rw [sweep, LinearMap.domRestrict_apply, sweepExtension_mk, dite_eq_left hn]

/-- A finite transverse presentation computes the sweep by sweeping every
nonzero cell once, with its original coefficient. -/
theorem sweep_ofFinsupp (n : N) (f : OrientedCell h (k + 1) →₀ E)
    (hf : ∀ σ ∈ f.support, i n ∉ (affineSpan ℝ σ.carrier).direction) :
    sweep n ⟨ofFinsupp (R := R) f,
        (mem_transverseSubmodule_iff_exists (i n) _).mpr ⟨f, hf, rfl⟩⟩ =
      ∑ σ : f.support, mk (σ.val.sweep n (hf σ.val σ.property)) (f σ.val) := by
  classical
  rw [sweep, LinearMap.domRestrict_apply]
  dsimp only [Subtype.coe_mk]
  have he : ofFinsupp (R := R) f = ∑ σ ∈ f.support, mk σ (f σ) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    simp only [Finsupp.sum, map_sum, ofFinsupp_single]
  rw [he, map_sum, ← Finset.sum_attach f.support]
  apply Finset.sum_congr rfl
  intro σ _
  rw [sweepExtension_mk, dite_eq_left (hf σ.val σ.property)]

/-- The sweep is the unique linear map with the prescribed values on
transverse generators. -/
theorem sweep_unique (n : N)
    (f : transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n) →ₗ[R]
      PolyhedralCochain R h E k)
    (hf : ∀ (σ : OrientedCell h (k + 1))
      (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) (c : E),
      f ⟨mk σ c, mk_mem_transverseSubmodule (i n) σ hn c⟩ = mk (σ.sweep n hn) c) :
    f = sweep n := by
  apply transverse_hom_ext (i n)
  intro σ hn c
  rw [hf σ hn c, sweep_mk]

section Coefficients

variable {E' : Type*} [AddCommGroup E'] [Module R E']

/-- Sweeping commutes with linear coefficient maps. -/
theorem map_sweep (f : E →ₗ[R] E') (n : N)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n)) :
    map f (sweep n C) = sweep n (transverseMap f (i n) C) := by
  have he : map f ∘ₗ sweep n = sweep n ∘ₗ transverseMap (h := h) (k := k + 1) f (i n) := by
    apply transverse_hom_ext (i n)
    intro σ hn c
    simp only [LinearMap.comp_apply]
    have hc : transverseMap f (i n) ⟨mk σ c, mk_mem_transverseSubmodule (i n) σ hn c⟩ =
        ⟨mk σ (f c), mk_mem_transverseSubmodule (i n) σ hn (f c)⟩ := by
      apply Subtype.ext
      simp
    rw [sweep_mk n σ hn c, map_mk, hc, sweep_mk n σ hn (f c)]
  exact LinearMap.congr_fun he C

end Coefficients

end Mei.PolyhedralCochain
