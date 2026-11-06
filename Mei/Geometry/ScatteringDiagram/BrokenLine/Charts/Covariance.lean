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

We use the existing affine equivalence of decorated types and affine covariance
of the backward hinge formula. The endpoint-chart interpretation follows
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

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k

local notation "E" => cutoffDecoratedTypeAffineEquiv d ℳ T a v f ε e k

variable (c : J → ℝ) (P W : J → Set V) (S : K → Set V) (C : Set V)

local notation "b" => fun j => c j - f j (e.symm 0)
local notation "D" => CutoffDecoratedType.domain c P W S C

/-- The continuous path extensions transform affinely at every endpoint,
including singular boundary paths, collapsed encounters and empty-domain types. -/
theorem cutoffDecoratedTypeAffineEquiv_path (t : Types) (Q : V) (s : ℝ) :
    (E t).path b (e Q) s = e (t.path c Q s) := by
  have hi := cutoffDecoratedTypeAffineEquiv_itinerary d ℳ T a v f ε e k t
  have hh := cutoffDecoratedTypeAffineEquiv_history d ℳ T a v f ε e k t
  -- Identify the dependent itinerary before rewriting its degree history.
  generalize ht : E t = t' at hi hh ⊢
  obtain ⟨l', history', dm', ds'⟩ := t'
  dsimp at hi hh
  cases hi
  simp only [CutoffDecoratedType.path_def]
  rw [eq_of_heq hh]
  exact backwardPath_affine _ _ _ e Q s

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
    · intro Q _ s
      simpa only [Toric.IntegralAffineEquiv.toContinuousAffineEquiv_apply] using
        cutoffDecoratedTypeAffineEquiv_path d ℳ T a v f ε
          A.toContinuousAffineEquiv k c t Q s
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
