/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor

/-!
# Tropical vertex labels with one normal are function-wall labels

Fix an integral normal `n` and let `T` be the allowed degrees tangent to `n`. A function
`c : T → R` gives the completed tangent series `∑_{q ≠ 0} c q z^q`
(`Mei.completedTangentSeries`), without constant term.

A completed tropical vertex label `g` whose logarithmic coefficients lie in the wall spaces of
their degrees and of `n` is the completed tangent label `exp(u ∂_n)` of such a series `u`
(`Mei.exists_eq_completedBCHExp_completedTropicalTangentField`); the coefficient of `z^q` in `u`
is the scalar of the degree-`q` logarithmic coefficient `u_q z^q ∂_n` of `g`. This is the
converse of `Mei.logComponent_completedBCHExp_completedTropicalTangentField_mem_wall`. Taking
`f = exp(u)`, which is congruent to one, `g = exp(log(f) ∂_n)` is the function-wall label of `f`
(`Mei.exists_eq_completedBCHExp_completedTropicalTangentField_completedLog`).

Every element of a tropical vertex wall group `(tropicalVertexWallSpaces d ρ).wallGroup w n`
satisfies the hypothesis
(`Mei.logComponent_mem_tropicalVertexWallSpaces_wall_of_mem_wallGroup`). So every tropical vertex
wall label, and every product of wall labels on one supported ray with one normal, is the
function-wall label of a completed tangent series
(`Mei.exists_eq_completedBCHExp_completedTropicalTangentField_completedLog_of_mem_wallGroup`).
This is the existence of the wall function of a wall or of a ray in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public section

open TauCeti (AlgFiltration)

open TauCeti (PositiveDegrees IsPositiveGrading SupportedRay)

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Λ]

section Monoid

variable [AddCommMonoid Γ] (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (n : Λ →+ ℤ)

local notation "χ" => AddMonoidHom.comp (Int.castAddHom R) n
local notation "T" => tropicalTangentMonoid d ρ χ
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d T
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

section Series

/-- The nonzero tangent degrees of degree at most `k` form a finite set. -/
theorem finite_tangentCutoff (k : ℕ) : {t : T | (t : Γ) ≠ 0 ∧ d.degree t ≤ k}.Finite :=
  ((d.finite_cutoff k).preimage Subtype.val_injective.injOn).subset fun t ht =>
    d.mem_cutoff.mpr ⟨(tropicalTangentMonoid_le d ρ χ) t.property, ht.2⟩

/-- The truncation `∑_{q ≠ 0, δ q ≤ k} c q z^q` of the tangent series of `c`. -/
def tangentSeriesTruncation (c : T → R) (k : ℕ) : R[T] :=
  ∑ t ∈ (finite_tangentCutoff d ρ n k).toFinset, single t (c t)

/-- In a nonzero degree of degree at most `k`, the coefficient of the truncation at `k` is that of
`c`. -/
theorem coeff_tangentSeriesTruncation_of_le (c : T → R) {k : ℕ} {t : T} (ht : (t : Γ) ≠ 0)
    (htk : d.degree t ≤ k) : (tangentSeriesTruncation d ρ n c k).coeff t = c t := by
  classical
  rw [tangentSeriesTruncation, coeff_sum, Finset.sum_apply', Finset.sum_eq_single_of_mem t
    ((finite_tangentCutoff (R := R) d ρ n k).mem_toFinset.mpr ⟨ht, htk⟩) fun s _ hst => by
      rw [coeff_single, Finsupp.single_apply, ite_eq_right_iff]
      exact fun h => (hst h).elim, coeff_single, Finsupp.single_apply, ite_eq_left_iff]
  exact fun h => (h rfl).elim

/-- Truncations lie in the first filtration ideal: nonzero allowed degrees are positive. -/
theorem tangentSeriesTruncation_mem_ideal_one (c : T → R) (k : ℕ) :
    tangentSeriesTruncation d ρ n c k ∈ (G).ideal 1 := by
  refine Submodule.sum_mem _ fun t ht => ?_
  rw [Set.Finite.mem_toFinset] at ht
  have hpos := d.degree_pos ((tropicalTangentMonoid_le d ρ χ) t.property) ht.1
  rw [TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  exact Or.inr ⟨t, AddSubmonoid.mem_comap.mpr ((tropicalTangentMonoid_le d ρ χ) t.property),
    by simpa using Int.add_one_le_iff.mpr hpos, 0,
    (zero_add t).symm⟩

/-- Two truncations differ by terms of degree above the smaller cutoff. -/
theorem tangentSeriesTruncation_sub_mem_ideal (c : T → R) {k l : ℕ} (h : k ≤ l) :
    tangentSeriesTruncation d ρ n c l - tangentSeriesTruncation d ρ n c k ∈ (G).ideal (k + 1) := by
  classical
  have hsub : (finite_tangentCutoff (R := R) d ρ n k).toFinset ⊆
      (finite_tangentCutoff (R := R) d ρ n l).toFinset :=
    fun t ht => by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht ⊢
      exact ⟨ht.1, ht.2.trans (by exact_mod_cast h)⟩
  rw [tangentSeriesTruncation, tangentSeriesTruncation, ← Finset.sum_sdiff hsub,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun t ht => ?_
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and, not_le] at ht
  rw [TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  exact Or.inr ⟨t, AddSubmonoid.mem_comap.mpr ((tropicalTangentMonoid_le d ρ χ) t.property),
    by simpa [Int.add_one_le_iff] using ht.2 ht.1.1, 0, (zero_add t).symm⟩

/-- The completed tangent series `∑_{q ≠ 0} c q z^q` of a coefficient function `c` on the
tangent degrees. Its constant term is zero. -/
def completedTangentSeries (c : T → R) : (G).completion :=
  ⟨fun k => Ideal.Quotient.mk _ (tangentSeriesTruncation d ρ n c k.unop),
    ((G).mem_completion_iff _).mpr fun h => by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      exact tangentSeriesTruncation_sub_mem_ideal d ρ n c h⟩

/-- At order `k`, the completed tangent series is the class of its truncation at `k`. -/
@[simp]
theorem projection_completedTangentSeries (c : T → R) (k : ℕ) :
    (G).projection k (completedTangentSeries d ρ n c) =
      Ideal.Quotient.mk _ (tangentSeriesTruncation d ρ n c k) := by
  rw [AlgFiltration.projection_apply, completedTangentSeries]

/-- The completed tangent series has no constant term. -/
theorem completedTangentSeries_mem_completionIdeal_one (c : T → R) :
    completedTangentSeries d ρ n c ∈ (G).completionIdeal 1 := by
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, projection_completedTangentSeries,
    Ideal.Quotient.eq_zero_iff_mem]
  exact tangentSeriesTruncation_mem_ideal_one d ρ n c 0

end Series

section Label

variable [Algebra ℚ R]

/-- An element of the wall space of a degree `q` and the normal `n` is a scalar multiple of
`z^q ∂_n`. -/
theorem exists_smul_single_eq_of_mem_tropicalVertexWallSpaces {q : Γ}
    {x : tropicalVertexLieAlgebra (R := R) d ρ} (hx : x ∈ (H).wall q n) :
    ∃ r : R, r • LogarithmicVectorField.single ρ q χ = (x : LogarithmicVectorField R Γ Λ ρ) := by
  by_cases hq : n (ρ q) = 0
  · exact (mem_tropicalVertexWallSpaces_iff_of_tangent d ρ q n hq x).mp hx
  · rw [(H).nontangent q n hq, Submodule.mem_bot] at hx
    exact ⟨0, by simp [hx]⟩

/-- The wall space of a degree that is not tangent to `n` is zero. -/
theorem tropicalVertexWallSpaces_wall_eq_bot_of_notMem_tropicalTangentMonoid {q : Γ}
    (hq : q ∉ T) : (H).wall q n = ⊥ := by
  rw [mem_tropicalTangentMonoid, not_and_or] at hq
  rcases hq with hq | hq
  · exact eq_bot_iff.mpr (((H).wall_le_piece q n).trans
      (IsPositiveGrading.eq_bot (d := d) q (Or.inl hq)).le)
  · exact (H).nontangent q n fun h0 => hq (by simp [h0])

variable [DecidableEq Γ] {d ρ n}

/-- **Labels with one normal are tangent labels.** A completed tropical vertex label whose
logarithmic coefficients lie in the wall spaces of their degrees and of the normal `n` is the
completed tangent label `exp(u ∂_n)` of a completed tangent coefficient `u` without constant
term. -/
theorem exists_eq_completedBCHExp_completedTropicalTangentField {g : d.completedBCHGroup ℒ}
    (hg : ∀ q, (d.logComponent ℒ g q : tropicalVertexLieAlgebra d ρ) ∈ (H).wall q n) :
    ∃ u ∈ (G).completionIdeal 1,
      d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ u) = g := by
  /- Read the scalar `c q` of every logarithmic coefficient `c q • z^q ∂_n` and take the
  completed tangent series of `c`. Both labels have the same logarithmic coefficients: in a
  nonzero tangent degree both are `c q • z^q ∂_n`, and in every other degree both lie in a zero
  space (the zero piece or a nontangent wall space). -/
  choose c hc using fun q => exists_smul_single_eq_of_mem_tropicalVertexWallSpaces d ρ n (hg q)
  refine ⟨completedTangentSeries d ρ n (fun t => c t),
    completedTangentSeries_mem_completionIdeal_one d ρ n _,
    d.ext_logComponent ℒ fun q => Subtype.ext ?_⟩
  rw [logComponent_completedBCHExp_completedTropicalTangentField_eq_decompose d ρ n _
    (projection_completedTangentSeries d ρ n _ _) (Int.self_le_toNat (d.degree q))]
  by_cases hqT : q ∈ T
  · by_cases hq0 : q = 0
    · subst hq0
      have h0 : (ℒ) 0 = ⊥ := IsPositiveGrading.eq_bot (d := d) 0 (Or.inr rfl)
      have : Subsingleton ((ℒ) 0) := by
        rw [h0]
        infer_instance
      exact congrArg Subtype.val (Subsingleton.elim _ _)
    refine Subtype.ext ?_
    rw [decompose_tropicalTangentField_apply d ρ n _ ⟨q, hqT⟩,
      coeff_tangentSeriesTruncation_of_le d ρ n (fun t => c t) (t := ⟨q, hqT⟩) hq0
        (Int.self_le_toNat _),
      coe_tropicalTangentField_single d ρ χ hq0, map_smul]
    exact hc q
  · have hbot := tropicalVertexWallSpaces_wall_eq_bot_of_notMem_tropicalTangentMonoid d ρ n hqT
    have h₁ := decompose_tropicalTangentField_mem_wall d ρ n
      (tangentSeriesTruncation d ρ n (fun t => c t) (d.degree q).toNat) q
    have h₂ := hg q
    rw [hbot, Submodule.mem_bot] at h₁ h₂
    rw [h₁, h₂]

/-- **Labels with one normal are function-wall labels.** A completed tropical vertex label whose
logarithmic coefficients lie in the wall spaces of their degrees and of the normal `n` is the
function-wall label `exp(log(f) ∂_n)` of a completed tangent series `f` congruent to one. -/
theorem exists_eq_completedBCHExp_completedTropicalTangentField_completedLog
    {g : d.completedBCHGroup ℒ}
    (hg : ∀ q, (d.logComponent ℒ g q : tropicalVertexLieAlgebra d ρ) ∈ (H).wall q n) :
    ∃ f : {u : (G).completion // u - 1 ∈ (G).completionIdeal 1},
      d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ ((G).completedLog f)) = g := by
  obtain ⟨u, hu, rfl⟩ := exists_eq_completedBCHExp_completedTropicalTangentField hg
  exact ⟨⟨(G).completedExp ⟨u, hu⟩, (G).completedExp_sub_one_mem _⟩, by
    rw [AlgFiltration.completedLog_completedExp]⟩

end Label

end Monoid

section Group

variable [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ} {ρ : Γ →+ Λ}
  (n : Λ →+ ℤ)

local notation "χ" => AddMonoidHom.comp (Int.castAddHom R) n
local notation "T" => tropicalTangentMonoid d ρ χ
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d T
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ


/-- The logarithmic coefficients of an element of a tropical vertex wall group lie in the wall
spaces of their degrees and of its normal. -/
theorem logComponent_mem_tropicalVertexWallSpaces_wall_of_mem_wallGroup {w : SupportedRay d}
    {g : d.completedBCHGroup ℒ} (hg : g ∈ (H).wallGroup w n) (q : Γ) :
    (d.logComponent ℒ g q : tropicalVertexLieAlgebra d ρ) ∈ (H).wall q n := by
  obtain ⟨y, hy, he⟩ := ((H).mem_truncatedRayLieSubalgebra w n _ _).mp
    (((H).mem_wallGroup w n g).mp hg (d.degree q).toNat)
  rw [d.logComponent_eq_decompose ℒ g (Int.self_le_toNat _) he]
  exact (H).decompose_mem_wall_of_mem_raySubmodule hy q

variable {n} in
/-- **Wall labels are function-wall labels.** Every element of a tropical vertex wall group with
normal `n`, for instance the label of a tropical vertex wall or a product of labels of walls on
one supported ray with normal `n`, is the function-wall label `exp(log(f) ∂_n)` of a completed
tangent series `f` congruent to one. -/
theorem exists_eq_completedBCHExp_completedTropicalTangentField_completedLog_of_mem_wallGroup
    {w : SupportedRay d} {g : d.completedBCHGroup ℒ} (hg : g ∈ (H).wallGroup w n) :
    ∃ f : {u : (G).completion // u - 1 ∈ (G).completionIdeal 1},
      d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ ((G).completedLog f)) = g :=
  exists_eq_completedBCHExp_completedTropicalTangentField_completedLog
    (logComponent_mem_tropicalVertexWallSpaces_wall_of_mem_wallGroup n hg)

end Group

end Mei
