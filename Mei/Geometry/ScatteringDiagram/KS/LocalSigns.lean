/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Sign
public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.LinearAlgebra.Dual.Order

/-!
# Local degree signs at arrangement walls

Near a relative-interior point of a bounded-degree arrangement wall, the signs
of nonvanishing retained degrees stay fixed. All retained degrees vanishing
there acquire the sign of any positive degree coorienting that wall. Thus the
two local sides move the entire middle sign algebra to the positive or negative
side together, as needed to compare sign factorizations across a wall.

Vanishing degree normals are positive multiples of the chosen normal: their
kernels are the wall direction and they are all positive at the degree
functional. This works with lineality and without saturation or finite
generation of the positive monoid.

This supplies the local sign geometry in the reconstruction argument of
Tom Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*,
§3.4 ([arXiv:1603.00416](https://arxiv.org/abs/1603.00416)). It uses the
whole-cell vanishing criterion from `Mei.Geometry.ScatteringDiagram.KS.Sign`
and Mathlib's finite intersection of neighborhoods.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open Set Filter Topology

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)
  {k : ℕ} {P : Set (V →L[ℝ] ℝ)} {m n : N} {θ : V →L[ℝ] ℝ}

/-- Retained normals vanishing at a wall interior are positive multiples of any
positive supporting degree normal, including when degrees are not primitive. -/
theorem exists_pos_smul_eval_eq_of_mem_intrinsicInterior_wall
    (hP : P ∈ (d.arrangementComplex h k).walls)
    (hm : m ∈ d.monoid) (hm0 : m ≠ 0) (hPm : ∀ φ ∈ P, φ (i m) = 0)
    (hθ : θ ∈ intrinsicInterior ℝ P) (hn : n ∈ d.cutoff k \ {0}) (hθn : θ (i n) = 0) :
    ∃ c : ℝ, 0 < c ∧
      c • (ContinuousLinearMap.apply ℝ ℝ (i m)).toLinearMap =
        (ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap := by
  let := h.continuousDual.finiteDimensional
  let v := h.continuousRealCharacter d.degree
  have hpos {a : N} (ha : a ∈ d.monoid) (ha0 : a ≠ 0) : 0 < v (i a) := by
    simpa [v] using (Int.cast_pos.mpr (d.degree_pos ha ha0) : (0 : ℝ) < d.degree a)
  have hnpos := hpos ((d.mem_cutoff).mp hn.1).1 hn.2
  have hmpos := hpos hm hm0
  have hne {a : N} (ha : 0 < v (i a)) :
      (ContinuousLinearMap.apply ℝ ℝ (i a)).toLinearMap ≠ 0 := by
    intro he
    exact ha.ne' (congrArg (fun f : (V →L[ℝ] ℝ) →ₗ[ℝ] ℝ => f v) he)
  have hPn := (d.eval_eq_zero_iff_forall_of_mem_intrinsicInterior_arrangementComplex h
    ((d.arrangementComplex h k).mem_cells_of_mem_walls hP) hθ hn).mp hθn
  have hdim := (d.arrangementComplex h k).finrank_direction_add_one_of_mem_walls hP
  have hkm := ((ContinuousLinearMap.apply ℝ ℝ (i m)).toLinearMap).ker_eq_direction_affineSpan
    (hne hmpos) hPm hdim
  have hkn := ((ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap).ker_eq_direction_affineSpan
    (hne hnpos) hPn hdim
  exact LinearMap.exists_pos_smul_eq_of_ker_le_ker _ _
    (hkm.trans hkn.symm).le hmpos hnpos

/-- In a neighborhood of a wall-interior point, all retained degree signs are
determined by their old nonzero signs and the side of one positive wall normal. -/
theorem eventually_sign_eq_of_mem_intrinsicInterior_wall
    (hP : P ∈ (d.arrangementComplex h k).walls)
    (hm : m ∈ d.monoid) (hm0 : m ≠ 0) (hPm : ∀ φ ∈ P, φ (i m) = 0)
    (hθ : θ ∈ intrinsicInterior ℝ P) :
    ∀ᶠ φ in 𝓝 θ, ∀ n ∈ d.cutoff k \ {0},
      SignType.sign (φ (i n)) =
        if θ (i n) = 0 then SignType.sign (φ (i m)) else SignType.sign (θ (i n)) := by
  classical
  have hrows : ∀ n : ↥(d.cutoff k \ {0}), ∀ᶠ φ in 𝓝 θ,
      SignType.sign (φ (i n)) =
        if θ (i n) = 0 then SignType.sign (φ (i m)) else SignType.sign (θ (i n)) := by
    intro n
    by_cases hz : θ (i n) = 0
    · obtain ⟨c, hc, he⟩ := d.exists_pos_smul_eval_eq_of_mem_intrinsicInterior_wall h
        hP hm hm0 hPm hθ n.property hz
      apply Eventually.of_forall
      intro φ
      have hv : c * φ (i m) = φ (i n) := by
        simpa using congrArg (fun f : (V →L[ℝ] ℝ) →ₗ[ℝ] ℝ => f φ) he
      simp only [hz, ↓reduceIte, ← hv, sign_mul, sign_pos hc, one_mul]
    · rcases lt_or_gt_of_ne hz with hneg | hpos
      · filter_upwards [((ContinuousLinearMap.apply ℝ ℝ (i n)).continuous.continuousAt).eventually
          (gt_mem_nhds hneg)] with φ hφ
        simp only [ContinuousLinearMap.apply_apply] at hφ
        simp [hz, sign_neg hφ, sign_neg hneg]
      · filter_upwards [((ContinuousLinearMap.apply ℝ ℝ (i n)).continuous.continuousAt).eventually
          (lt_mem_nhds hpos)] with φ hφ
        simp only [ContinuousLinearMap.apply_apply] at hφ
        simp [hz, sign_pos hφ, sign_pos hpos]
  filter_upwards [Filter.eventually_all.mpr hrows] with φ hφ n hn
  exact hφ ⟨n, hn⟩

end Mei.PositiveDegrees
