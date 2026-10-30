/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Covariance

/-!
# Affine covariance across all cutoff encounter itineraries

Affine coordinate changes identify the entire finite-cutoff decorated ray family,
with no assumed encounter bound or endpoint genericity. The equivalence preserves
every recorded encounter, degree, parameter and whole decoration, and maps the
entire geometric path. It therefore preserves finite weighted evaluation.

Supports, singular sets and the incoming source move by the same affine map.
Normals use its inverse linear part and offsets include the translation. Thus
orientation-reversing maps require no additional sign. Coefficients and degree
labels are retained; intertwining coefficient changes can be applied separately.

We use `decoratedRayAffineEquiv` on each itinerary and the existing
`CutoffDecoratedRay` family. The geometric comparison follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2); whole-component decorations follow
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definitions 3.1–3.3 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V V' J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  (T : J → Module.End R M) (a : ℳ 0) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)
  (e : V ≃ᴬ[ℝ] V') (k : ℕ) (Q : V)

local notation "g" => fun j =>
  ContinuousLinearMap.comp (f j) e.symm.toContinuousAffineMap.contLinear
local notation "b" => fun j => c j - f j (e.symm 0)
local notation "u" => fun p => e.toAffineEquiv.linear (v p)
local notation "Source" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
local notation "Target" => CutoffDecoratedRay d ℳ T a u g b ε
  (fun j => e '' P j) (fun j => e '' W j)
  (fun j => e '' S j) (e '' C) k (e Q)

/-- Affine coordinate changes identify the full cutoff evaluation fibers over
all finite encounter words. No rationality or genericity assumption is required. -/
def cutoffDecoratedRayAffineEquiv : Source ≃ Target where
  toFun r := ⟨r.itinerary,
    decoratedRayAffineEquiv ℳ (fun j => T (r.itinerary.get j)) 0 a v
      (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
      (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q
      r.realization,
    by simpa only [decoratedRayAffineEquiv_history] using r.degree_mem,
    by simpa only [decoratedRayAffineEquiv_history] using r.degree_sub_mem⟩
  invFun r := ⟨r.itinerary,
    (decoratedRayAffineEquiv ℳ (fun j => T (r.itinerary.get j)) 0 a v
      (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
      (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q).symm
      r.realization,
    by simpa only [decoratedRayAffineEquiv_symm_history] using r.degree_mem,
    by simpa only [decoratedRayAffineEquiv_symm_history] using r.degree_sub_mem⟩
  left_inv r := by
    apply CutoffDecoratedRay.ext
    · rfl
    exact heq_of_eq (Equiv.symm_apply_apply _ _)
  right_inv r := by
    apply CutoffDecoratedRay.ext
    · rfl
    exact heq_of_eq (Equiv.apply_symm_apply _ _)

/-- All encounters, including those with unchanged degree, retain their labels. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_itinerary (r : Source) :
    (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r).itinerary =
      r.itinerary := (rfl)

/-- The inverse comparison keeps the full encounter itinerary. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_symm_itinerary (r : Target) :
    ((cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q).symm r).itinerary =
      r.itinerary := (rfl)

/-- The entire degree history is unchanged, including shifts of zero spatial direction. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_history (r : Source) :
    HEq (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r).realization.1.val
      r.realization.1.val :=
  heq_of_eq (decoratedRayAffineEquiv_history ℳ (fun j => T (r.itinerary.get j))
    0 a v (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
    (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q r.realization)

/-- Every segment retains its whole homogeneous decoration. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_segmentDecorations (r : Source) :
    HEq (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r).realization.decoration
      r.realization.decoration :=
  heq_of_eq (funext (decoratedRayAffineEquiv_decoration ℳ
    (fun j => T (r.itinerary.get j)) 0 a v
    (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
    (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q r.realization))

/-- Affine coordinate changes preserve the complete geometric path. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_ray (r : Source) :
    (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r).realization.2.ray =
      r.realization.2.ray.map e.toAffineEquiv.toAffineMap :=
  decoratedRayAffineEquiv_ray ℳ (fun j => T (r.itinerary.get j))
    0 a v (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
    (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q r.realization

/-- Every encounter time is retained across the complete cutoff family. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_parameter (r : Source) :
    HEq (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r).realization.2.parameter
      r.realization.2.parameter :=
  heq_of_eq (decoratedRayAffineEquiv_parameter ℳ (fun j => T (r.itinerary.get j))
    0 a v (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
    (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q r.realization)

/-- The final whole decoration is unchanged by an affine coordinate change. -/
@[simp↓]
theorem cutoffDecoratedRayAffineEquiv_decoration (r : Source) :
    (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r).decoration =
      r.decoration := by
  simp only [CutoffDecoratedRay.decoration_eq, cutoffDecoratedRayAffineEquiv,
    Equiv.coe_fn_mk, decoratedRayAffineEquiv_history]

/-- The inverse comparison keeps the complete degree history. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_symm_history (r : Target) :
    HEq ((cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q).symm r).realization.1.val
      r.realization.1.val :=
  heq_of_eq (decoratedRayAffineEquiv_symm_history ℳ (fun j => T (r.itinerary.get j))
    0 a v (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
    (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q r.realization)

/-- Inverse affine transport recovers the whole geometric path. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_symm_ray (r : Target) :
    ((cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q).symm r).realization.2.ray =
      r.realization.2.ray.map e.symm.toAffineEquiv.toAffineMap :=
  decoratedRayAffineEquiv_symm_ray ℳ (fun j => T (r.itinerary.get j))
    0 a v (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
    (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q r.realization

/-- The inverse comparison preserves every encounter parameter. -/
@[simp]
theorem cutoffDecoratedRayAffineEquiv_symm_parameter (r : Target) :
    HEq
      ((cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q).symm r).realization.2.parameter
      r.realization.2.parameter :=
  heq_of_eq (decoratedRayAffineEquiv_symm_parameter ℳ (fun j => T (r.itinerary.get j))
    0 a v (fun j => f (r.itinerary.get j)) (fun j => c (r.itinerary.get j))
    (fun j => ε (r.itinerary.get j)) (fun j => P (r.itinerary.get j)) W S C e Q r.realization)

/-- Inverse affine transport preserves the whole final decoration. -/
@[simp↓]
theorem cutoffDecoratedRayAffineEquiv_symm_decoration (r : Target) :
    ((cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q).symm r).decoration =
      r.decoration := by
  have he := cutoffDecoratedRayAffineEquiv_decoration d ℳ T a v f c ε P W S C e k Q
    ((cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q).symm r)
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

/-- The full finite-cutoff weighted evaluation is affine covariant. All
contributing paths are compared, including their incoming tails outside a local
endpoint neighborhood. No consistency or genericity hypothesis is imposed. -/
@[simp]
theorem cutoffDecoratedEvaluation_affine [Finite J] :
    cutoffDecoratedEvaluation d ℳ T a u g b ε
      (fun j => e '' P j) (fun j => e '' W j)
      (fun j => e '' S j) (e '' C) k (e Q) =
        cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q := by
  classical
  let := Fintype.ofFinite Source
  let := Fintype.ofFinite Target
  simp only [cutoffDecoratedEvaluation_def]
  exact (Fintype.sum_equiv (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q)
    _ _ (fun r => (cutoffDecoratedRayAffineEquiv_decoration
      d ℳ T a v f c ε P W S C e k Q r).symm)).symm

end Mei
