/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Basic
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Regrading.Coefficient

/-!
# Coefficient embeddings of closed decorated-type charts

An injective intertwining coefficient map and a degree isomorphism identify
complete cutoff decorated types, including types with empty endpoint domains.
The comparison preserves their encounter words, regrades their entire histories,
and maps their whole final decorations. Their endpoint domains and continuous
path extensions agree, including singular boundary paths and incoming tails.
Consequently closed polyhedral subdivisions transport in both directions.

The construction uses the whole-history coefficient comparison
`map_homogeneousHistory_of_injective` and the existing backward path extension.
The interpretation of closed endpoint charts follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M N Γ Δ V J K I : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Δ] [DecidableEq Δ]
  (d : PositiveDegrees Γ) (e : PositiveDegrees Δ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ ≃+ Δ) (hinj : Function.Injective r)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (U : J → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (a : ℳ 0) (v : Γ → V) (w : Δ → V) (hv : ∀ p, v p = w (σ p))
  (f : J → V →L[ℝ] ℝ) (ε : J → SignType)
  (k l : ℕ) (hcut : ∀ p, p ∈ d.cutoff k ↔ σ p ∈ e.cutoff l)
  (hpos : ∀ p, p ∈ d.monoid ↔ σ p ∈ e.monoid)

local notation "a'" => regradeBase ℳ 𝓝 r (σ : Γ →+ Δ) hr a
local notation "Source" => CutoffDecoratedType d ℳ T a v f ε k
local notation "Target" => CutoffDecoratedType e 𝓝 U a' w f ε l

local notation "E" => cutoffDecoratedTypeCoefficientEquiv d e ℳ 𝓝 r σ hinj hr
  T U hT a v w hv f ε k l hcut hpos

variable (c : J → ℝ) (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)

/-- The continuous path extensions agree at every endpoint and every time,
including singular degenerations, collapsed encounters and the incoming tail. -/
@[simp]
theorem cutoffDecoratedTypeCoefficientEquiv_path (t : Source) :
    (E t).path c = t.path c := by
  have hw := cutoffDecoratedTypeCoefficientEquiv_itinerary d e ℳ 𝓝 r σ hinj hr
    T U hT a v w hv f ε k l hcut hpos t
  have hh := cutoffDecoratedTypeCoefficientEquiv_history d e ℳ 𝓝 r σ hinj hr
    T U hT a v w hv f ε k l hcut hpos t
  generalize E t = u at hw hh ⊢
  rw [CutoffDecoratedType.path_def, CutoffDecoratedType.path_def]
  -- Align the dependent history domains using the preserved encounter word.
  rcases t with ⟨⟨word, _⟩, p, _, _⟩
  rcases u with ⟨⟨word', _⟩, q, _, _⟩
  dsimp only at hw hh ⊢
  cases hw
  rw [eq_of_heq hh]
  congr 1
  funext j
  rw [hv, ← σ.map_zero, ← Fin.comp_snoc]
  rfl

/-- Any closed polyhedral subdivision transports in both directions along a
coefficient embedding. The chart sets and their indices stay the same, reindexed
by the type equivalence, and both proper endpoint and path maps are retained.
No admissibility is asserted for a boundary path. -/
theorem cutoffDecoratedTypeCoefficientEquiv_closedCharts
    {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
    (h : TauCeti.Toric.IsIntegralLattice i)
    (κ : Source → Type*) (B : ∀ t, κ t → Set V) :
    ((∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        B t j ⊆ closure (CutoffDecoratedType.domain c P W S C t) ∧
        IsProperMap (fun Q : B t j => (Q : V)) ∧
        IsProperMap (fun Q : B t j => t.path c Q.val)) ∧
      (∀ t, Pairwise fun j z => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t z))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = CutoffDecoratedType.domain c P W S C t)) ↔
    ((∀ t j, (B ((E).symm t) j).Nonempty ∧
        IsRationalNormalPolyhedron h (B ((E).symm t) j) ∧
        B ((E).symm t) j ⊆ closure (CutoffDecoratedType.domain c P W S C t) ∧
        IsProperMap (fun Q : B ((E).symm t) j => (Q : V)) ∧
        IsProperMap (fun Q : B ((E).symm t) j => t.path c Q.val)) ∧
      (∀ t, Pairwise fun j z => Disjoint (intrinsicInterior ℝ (B ((E).symm t) j))
        (intrinsicInterior ℝ (B ((E).symm t) z))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B ((E).symm t) j) =
        CutoffDecoratedType.domain c P W S C t)) := by
  have hD := cutoffDecoratedTypeCoefficientEquiv_domain d e ℳ 𝓝 r σ hinj hr
    T U hT a v w hv f ε k l hcut hpos c P W S C
  have hpath := cutoffDecoratedTypeCoefficientEquiv_path d e ℳ 𝓝 r σ hinj hr
    T U hT a v w hv f ε k l hcut hpos c
  constructor
  · rintro ⟨hB, hdisj, hcover⟩
    refine ⟨?_, fun t => hdisj ((E).symm t), ?_⟩
    · intro t j
      have hd := hD ((E).symm t)
      have hp := hpath ((E).symm t)
      rw [Equiv.apply_symm_apply] at hd hp
      simpa only [hd, hp] using hB ((E).symm t) j
    · intro t
      have hd := hD ((E).symm t)
      rw [Equiv.apply_symm_apply] at hd
      exact (hcover ((E).symm t)).trans hd.symm
  · rintro ⟨hB, hdisj, hcover⟩
    refine ⟨?_, ?_, ?_⟩
    · intro t j
      have hb := hB (E t)
      rw [(E).symm_apply_apply t] at hb
      simpa only [hD t, hpath t] using hb j
    · intro t
      have hd := hdisj (E t)
      rw [(E).symm_apply_apply t] at hd
      exact hd
    · intro t
      have hc := hcover (E t)
      rw [(E).symm_apply_apply t, hD t] at hc
      exact hc

end Mei
