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
Complete decorated types and their endpoint domains are transported as well,
with homeomorphic domain closures even for types with empty domains.

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

section Rays

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

end Rays

section TypeTransport

variable {R M Γ V V' J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  (T : J → Module.End R M) (a : ℳ 0) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (ε : J → SignType) (e : V ≃ᴬ[ℝ] V') (k : ℕ)

local notation "g" => fun j =>
  ContinuousLinearMap.comp (f j) e.symm.toContinuousAffineMap.contLinear
local notation "u" => fun p => e.toAffineEquiv.linear (v p)
local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k
local notation "Types'" => CutoffDecoratedType d ℳ T a u g ε k

/-- Affine transport retains the entire encounter word and degree history of a
cutoff type, including types whose endpoint domains are empty. -/
def cutoffDecoratedTypeAffineEquiv : Types ≃ Types' where
  toFun t := ⟨t.itinerary, ⟨t.history.val, by
    rw [decoratedHistorySupport_affine]
    exact t.history.property⟩, t.degree_mem, t.degree_sub_mem⟩
  invFun t := ⟨t.itinerary, ⟨t.history.val, by
    rw [← decoratedHistorySupport_affine ℳ (fun j => T (t.itinerary.val.get j))
      0 a v (fun j => f (t.itinerary.val.get j)) (fun j => ε (t.itinerary.val.get j)) e]
    exact t.history.property⟩, t.degree_mem, t.degree_sub_mem⟩
  left_inv _ := rfl
  right_inv _ := rfl

local notation "E" => cutoffDecoratedTypeAffineEquiv d ℳ T a v f ε e k

/-- Coordinate changes retain the full encounter itinerary. -/
@[simp]
theorem cutoffDecoratedTypeAffineEquiv_itinerary (t : Types) :
    (E t).itinerary = t.itinerary := (rfl)

/-- Coordinate changes retain every degree label in the history. -/
@[simp]
theorem cutoffDecoratedTypeAffineEquiv_history (t : Types) :
    HEq (E t).history.val t.history.val := (HEq.rfl)

/-- The weight attached to a closed chart is unchanged by affine transport. -/
@[simp↓]
theorem cutoffDecoratedTypeAffineEquiv_decoration (t : Types) :
    (E t).decoration = t.decoration := by
  simp only [CutoffDecoratedType.decoration_eq, cutoffDecoratedTypeAffineEquiv, Equiv.coe_fn_mk]

variable (c : J → ℝ) (P W : J → Set V) (S : K → Set V) (C : Set V)

local notation "b" => fun j => c j - f j (e.symm 0)
local notation "P'" => fun j => e '' P j
local notation "W'" => fun j => e '' W j
local notation "S'" => fun j => e '' S j
local notation "D" => CutoffDecoratedType.domain c P W S C
local notation "D'" => CutoffDecoratedType.domain b P' W' S' (e '' C)

/-- Admissibility of a complete type is invariant under affine coordinates.
All obstacles and the original incoming source are transported together. -/
@[simp↓] -- Transport the domain before the general admissibility expansion.
theorem mem_cutoffDecoratedTypeAffineEquiv_domain (t : Types) (Q : V) :
    e Q ∈ D' (E t) ↔ Q ∈ D t := by
  simp only [CutoffDecoratedType.domain_def, cutoffDecoratedTypeAffineEquiv, Equiv.coe_fn_mk]
  rw [← nonempty_admissibleRayRealization_iff, ← nonempty_admissibleRayRealization_iff]
  exact (admissibleRayAffineEquiv (fun j => f (t.itinerary.val.get j))
    (fun j => c (t.itinerary.val.get j))
    (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j))
    (fun j => P (t.itinerary.val.get j)) W S C e Q).nonempty_congr.symm

/-- The new endpoint domain is exactly the image of the old one. -/
theorem cutoffDecoratedTypeAffineEquiv_domain (t : Types) :
    D' (E t) = e '' D t := by
  ext Y
  obtain ⟨Q, rfl⟩ := e.surjective Y
  simp only [mem_cutoffDecoratedTypeAffineEquiv_domain, e.injective.mem_set_image]

/-- Closing endpoint domains commutes with affine transport, including for
empty domains and lower-dimensional branches. -/
theorem cutoffDecoratedTypeAffineEquiv_closure_domain (t : Types) :
    closure (D' (E t)) = e '' closure (D t) := by
  rw [cutoffDecoratedTypeAffineEquiv_domain]
  exact (e.toHomeomorph.image_closure _).symm

/-- The type comparison agrees with the existing affine comparison of actual
ray fibers. Thus the closed charts retain the original global histories. -/
@[simp↓] -- Compare types before expanding the ray-to-type structure.
theorem cutoffDecoratedRayAffineEquiv_type [Finite J] (Q : V)
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    (cutoffDecoratedRayFiberEquiv d ℳ T a u g b ε P' W' S' (e '' C) k (e Q)
      (cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r)).val =
      E (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val := by
  have hi := cutoffDecoratedRayAffineEquiv_itinerary d ℳ T a v f c ε P W S C e k Q r
  have hh := cutoffDecoratedRayAffineEquiv_history d ℳ T a v f c ε P W S C e k Q r
  -- Identify the dependent encounter index before comparing the two history subtypes.
  generalize hr : cutoffDecoratedRayAffineEquiv d ℳ T a v f c ε P W S C e k Q r = r' at *
  obtain ⟨l, real, dm, ds⟩ := r
  obtain ⟨l', real', dm', ds'⟩ := r'
  dsimp at hi hh
  cases hi
  simp only [cutoffDecoratedRayFiberEquiv_apply_val, cutoffDecoratedTypeAffineEquiv,
    Equiv.coe_fn_mk]
  apply CutoffDecoratedType.ext
  · rfl
  · exact heq_of_eq (Subtype.ext (eq_of_heq hh))

/-- Each full closed type domain is homeomorphic to its transported domain.
The map is the original affine map, so compact endpoint sets are preserved. -/
def cutoffDecoratedTypeClosedDomainHomeomorph (t : Types) :
    closure (D t) ≃ₜ closure (D' (E t)) :=
  e.toHomeomorph.subtype fun Q => by
    rw [cutoffDecoratedTypeAffineEquiv_closure_domain]
    exact e.injective.mem_set_image.symm

/-- The closed-domain comparison transports the endpoint by the same affine map. -/
@[simp]
theorem cutoffDecoratedTypeClosedDomainHomeomorph_apply (t : Types) (Q : closure (D t)) :
    (cutoffDecoratedTypeClosedDomainHomeomorph d ℳ T a v f ε e k c P W S C t Q).val =
      e Q.val := (rfl)

/-- The inverse closed-domain comparison pulls endpoints back by the inverse map. -/
@[simp]
theorem cutoffDecoratedTypeClosedDomainHomeomorph_symm_apply (t : Types)
    (Q : closure (D' (E t))) :
    ((cutoffDecoratedTypeClosedDomainHomeomorph d ℳ T a v f ε e k c P W S C t).symm Q).val =
      e.symm Q.val := (rfl)

end TypeTransport

end Mei
