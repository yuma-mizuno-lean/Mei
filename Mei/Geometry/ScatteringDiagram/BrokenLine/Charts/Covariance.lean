/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Covariance

/-!
# Affine transport of closed decorated-type charts

Affine coordinate changes transport complete decorated types and their full endpoint
domains. Taking closures commutes with this transport, and the continuous path
extensions agree even at collapsed or singular encounters. Consequently a closed
endpoint chart can be transported with its original type and whole weight, rather
than choosing a new subdivision in the new coordinates. Incoming tails are part of
the transported paths; boundary paths are not asserted to be admissible.

We use the existing affine equivalence of admissible rays and uniqueness of continuous
extensions from a set to its closure. The endpoint-chart interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
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

/-- The continuous path extensions transform affinely on the entire closed
domain, including singular boundary paths and collapsed encounters. -/
theorem cutoffDecoratedTypeAffineEquiv_path (t : Types) {Q : V}
    (hQ : Q ∈ closure (D t)) (s : ℝ) :
    (E t).path b (e Q) s = e (t.path c Q s) := by
  have heq : Set.EqOn (fun X => (E t).path b (e X) s)
      (fun X => e (t.path c X s)) (D t) := by
    intro X hX
    let r := admissibleRayRealization (fun j => f (t.itinerary.val.get j))
      (fun j => c (t.itinerary.val.get j))
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j))
      (fun j => P (t.itinerary.val.get j)) W S C X
      ((CutoffDecoratedType.mem_domain c P W S C t X).mp hX)
    let r' := admissibleRayAffineEquiv (fun j => f (t.itinerary.val.get j))
      (fun j => c (t.itinerary.val.get j))
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j))
      (fun j => P (t.itinerary.val.get j)) W S C e X r
    simp only [CutoffDecoratedType.path_def, cutoffDecoratedTypeAffineEquiv, Equiv.coe_fn_mk]
    rw [← r'.toContinuousMap_eq_backwardPath,
      FiniteAffineRay.toContinuousMap_apply, admissibleRayAffineEquiv_ray,
      FiniteAffineRay.map_apply, ← FiniteAffineRay.toContinuousMap_apply,
      r.toContinuousMap_eq_backwardPath]
    rfl
  exact heq.closure (by fun_prop) (by fun_prop) hQ

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

section Integral

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  (A : Toric.IntegralAffineEquiv h h')

local notation "Eᵢ" =>
  cutoffDecoratedTypeAffineEquiv d ℳ T a v f ε A.toContinuousAffineEquiv k
local notation "bᵢ" => fun j => c j - f j (A.toContinuousAffineEquiv.symm 0)
local notation "Dᵢ" => CutoffDecoratedType.domain bᵢ
  (fun j => A '' P j) (fun j => A '' W j) (fun j => A '' S j) (A '' C)

/-- Transport any closed polyhedral chart subdivision of the full type domains
without changing its index set. The images still exhaust every transported type,
with disjoint interiors within each type, and have proper endpoint and path maps.
The path identity includes all boundary degenerations and the full incoming tail. -/
theorem cutoffDecoratedTypeAffineEquiv_closedCharts
    (ι : Types → Type*) (B : ∀ t, ι t → Set V)
    (hB : ∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
      B t j ⊆ closure (D t))
    (hdisj : ∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
      (intrinsicInterior ℝ (B t l)))
    (hcover : ∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = D t) :
    (∀ t j, (A '' B t j).Nonempty ∧ IsRationalNormalPolyhedron h' (A '' B t j) ∧
      A '' B t j ⊆ closure (Dᵢ (Eᵢ t)) ∧
      IsProperMap (fun Q : A '' B t j => (Q : V')) ∧
      IsProperMap (fun Q : A '' B t j => (Eᵢ t).path bᵢ Q.val) ∧
      ∀ Q ∈ B t j, ∀ s : ℝ, (Eᵢ t).path bᵢ (A Q) s = A (t.path c Q s)) ∧
    (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (A '' B t j))
      (intrinsicInterior ℝ (A '' B t l))) ∧
    ∀ t, ⋃ j, intrinsicInterior ℝ (A '' B t j) = Dᵢ (Eᵢ t) := by
  have hsub (t : Types) (j : ι t) : A '' B t j ⊆ closure (Dᵢ (Eᵢ t)) := by
    simp only [← Toric.IntegralAffineEquiv.toContinuousAffineEquiv_apply]
    rw [cutoffDecoratedTypeAffineEquiv_closure_domain]
    exact Set.image_mono (hB t j).2.2
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    have hpoly := (hB t j).2.1.image A
    refine ⟨(hB t j).1.image A, hpoly, hsub t j,
      hpoly.isClosed.isProperMap_subtypeVal, ?_, ?_⟩
    · rw [CutoffDecoratedType.path_def]
      exact isProperMap_backwardPath_restrict _ _ _ hpoly.isClosed
        (fun Q hQ => (Eᵢ t).backwardTime_nonneg bᵢ
          (fun j => A '' P j) (fun j => A '' W j) (fun j => A '' S j) (A '' C)
          (hsub t j hQ))
    · intro Q hQ s
      simpa only [Toric.IntegralAffineEquiv.toContinuousAffineEquiv_apply] using
        cutoffDecoratedTypeAffineEquiv_path d ℳ T a v f ε
          A.toContinuousAffineEquiv k c P W S C t ((hB t j).2.2 hQ) s
  · intro t j l hjl
    simp only [← Toric.IntegralAffineEquiv.toContinuousAffineEquiv_apply,
      ContinuousAffineEquiv.intrinsicInterior_image]
    exact Set.disjoint_image_of_injective A.toContinuousAffineEquiv.injective (hdisj t hjl)
  · intro t
    simp only [← Toric.IntegralAffineEquiv.toContinuousAffineEquiv_apply,
      ContinuousAffineEquiv.intrinsicInterior_image]
    rw [← Set.image_iUnion, hcover, cutoffDecoratedTypeAffineEquiv_domain]

end Integral

end Mei
