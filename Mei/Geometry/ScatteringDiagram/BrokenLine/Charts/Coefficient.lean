/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Regrading

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

include hinj hr hT hv in
private theorem base_support_iff (word : List J) (p : Fin word.length → Γ) :
    σ ∘ p ∈ decoratedHistorySupport 𝓝 (fun j => U (word.get j)) 0 a' w
        (fun j => f (word.get j)) (fun j => ε (word.get j)) ↔
      p ∈ decoratedHistorySupport ℳ (fun j => T (word.get j)) 0 a v
        (fun j => f (word.get j)) (fun j => ε (word.get j)) := by
  have hs := mem_decoratedHistorySupport_regrading_iff ℳ 𝓝 r σ hr σ.injective
    (fun j => T (word.get j)) (fun j => U (word.get j)) (fun j => hT (word.get j))
    0 a v w hv (fun j => f (word.get j)) (fun j => ε (word.get j)) hinj p
  -- The incoming target degree is zero, with its coefficient transported along `map_zero`.
  rw [mem_decoratedHistorySupport, mem_decoratedHistorySupport] at hs ⊢
  rw [coe_regradeBase ℳ 𝓝 r (σ : Γ →+ Δ) hr a]
  simpa only [map_zero] using hs

/-- Embed a complete decorated type by mapping its whole coefficients and
regrading every selected degree. No realization or generic endpoint is required. -/
private def coefficientMap (t : Source) : Target where
  itinerary := ⟨t.itinerary.val, by
    have hc := Nat.card_congr (σ.toEquiv.subtypeEquiv hcut)
    simpa only [hc] using t.itinerary.property⟩
  history := ⟨σ ∘ t.history.val,
    (base_support_iff ℳ 𝓝 r σ hinj hr T U hT a v w hv f ε t.itinerary.val _).mpr
      t.history.property⟩
  degree_mem j := (hcut _).mp (t.degree_mem j)
  degree_sub_mem i j hij := by
    simpa only [Function.comp_apply, map_sub] using (hpos _).mp (t.degree_sub_mem i j hij)

local notation "mapType" => coefficientMap d e ℳ 𝓝 r σ hinj hr
  T U hT a v w hv f ε k l hcut hpos

/-- Coefficient embeddings retain every encounter, including unchanged degrees. -/
@[simp]
private theorem coefficientMap_itinerary (t : Source) :
    (mapType t).itinerary.val = t.itinerary.val := (rfl)

private theorem coefficientMap_bijective : Function.Bijective mapType := by
  constructor
  · rintro ⟨word, p, hp, hm⟩ ⟨word', q, hq, hn⟩ he
    have hw := congrArg (fun t : Target => t.itinerary.val) he
    simp only [coefficientMap_itinerary] at hw
    have hw' : word = word' := Subtype.ext hw
    subst word'
    suffices hpq : p = q by cases hpq; rfl
    have hh := congrArg (fun t : Target => (⟨t.itinerary.val, t.history.val⟩ :
      Σ word : List J, Fin word.length → Δ)) he
    have hhist := (Sigma.mk.inj_iff.mp hh).2
    apply Subtype.ext
    exact funext fun j => σ.injective (congrFun (eq_of_heq hhist) j)
  · intro t
    let p := σ.symm ∘ t.history.val
    have hp : σ ∘ p = t.history.val := by funext j; simp [p]
    have hc := Nat.card_congr (σ.toEquiv.subtypeEquiv hcut)
    let s : Source := {
      itinerary := ⟨t.itinerary.val, by simpa only [hc] using t.itinerary.property⟩
      history := ⟨p, (base_support_iff ℳ 𝓝 r σ hinj hr T U hT a v w hv f ε
        t.itinerary.val p).mp (hp ▸ t.history.property)⟩
      degree_mem := fun j => (hcut _).mpr (by simpa [p] using t.degree_mem j)
      degree_sub_mem := fun i j hij => (hpos _).mpr (by
        simpa [p] using t.degree_sub_mem i j hij) }
    refine ⟨s, CutoffDecoratedType.ext rfl ?_⟩
    exact heq_of_eq (Subtype.ext hp)

/-- Injective coefficient transport and a degree isomorphism identify all
complete types at corresponding cutoffs, including unrealized types. -/
def cutoffDecoratedTypeCoefficientEquiv : Source ≃ Target :=
  Equiv.ofBijective mapType
    (coefficientMap_bijective d e ℳ 𝓝 r σ hinj hr T U hT a v w hv f ε k l hcut hpos)

local notation "E" => cutoffDecoratedTypeCoefficientEquiv d e ℳ 𝓝 r σ hinj hr
  T U hT a v w hv f ε k l hcut hpos

/-- The type equivalence applies the explicit history transport. -/
private theorem coefficientEquiv_apply (t : Source) : E t = mapType t :=
  Equiv.ofBijective_apply ..

/-- The type equivalence retains the complete encounter word. -/
@[simp]
theorem cutoffDecoratedTypeCoefficientEquiv_itinerary (t : Source) :
    (E t).itinerary.val = t.itinerary.val := (rfl)

/-- The type equivalence regrades the full degree history. -/
@[simp]
theorem cutoffDecoratedTypeCoefficientEquiv_history (t : Source) :
    HEq (E t).history.val (σ ∘ t.history.val) := (HEq.rfl)

/-- Whole final decorations are sent through the coefficient embedding. -/
@[simp↓]
theorem cutoffDecoratedTypeCoefficientEquiv_decoration (t : Source) :
    (E t).decoration = r t.decoration := by
  rw [coefficientEquiv_apply, coefficientMap,
    CutoffDecoratedType.decoration_eq, CutoffDecoratedType.decoration_eq]
  rw [coe_regradeBase ℳ 𝓝 r (σ : Γ →+ Δ) hr a]
  exact (map_homogeneousHistory_of_injective ℳ 𝓝 r σ hr σ.injective
    (fun j => T (t.itinerary.val.get j)) (fun j => U (t.itinerary.val.get j))
    (fun j => hT (t.itinerary.val.get j)) t.history.val a).symm

variable (c : J → ℝ) (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)

/-- The full endpoint domain is unchanged: incoming-source admission and
avoidance of unrecorded walls and singularities are preserved together. -/
@[simp]
theorem cutoffDecoratedTypeCoefficientEquiv_domain (t : Source) :
    CutoffDecoratedType.domain c P W S C (E t) =
      CutoffDecoratedType.domain c P W S C t := by
  rw [coefficientEquiv_apply, coefficientMap,
    CutoffDecoratedType.domain_def, CutoffDecoratedType.domain_def]
  dsimp only
  congr 1
  funext j
  rw [hv, ← σ.map_zero, ← Fin.comp_snoc]
  rfl

/-- The continuous path extensions agree at every endpoint and every time,
including singular degenerations, collapsed encounters and the incoming tail. -/
@[simp]
theorem cutoffDecoratedTypeCoefficientEquiv_path (t : Source) :
    (E t).path c = t.path c := by
  rw [coefficientEquiv_apply, coefficientMap,
    CutoffDecoratedType.path_def, CutoffDecoratedType.path_def]
  dsimp only
  congr 1
  funext j
  rw [hv, ← σ.map_zero, ← Fin.comp_snoc]
  rfl

/-- On actual rays, the type comparison is exactly the existing full
coefficient-embedding comparison, rather than a second choice of history. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_type [Finite J] (Q : V)
    (β : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    (cutoffDecoratedRayFiberEquiv e 𝓝 U a' w f c ε P W S C l Q
      (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r (σ : Γ →+ Δ)
        σ.injective hr T U hT a v w hv f c ε P W S C k l hcut hpos Q hinj β)).val =
      E ((cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q β).val) := by
  apply CutoffDecoratedType.ext_val
  · simp only [cutoffDecoratedRayFiberEquiv_apply_val,
      cutoffDecoratedTypeCoefficientEquiv_itinerary]
    exact cutoffDecoratedRayRegradingEmbeddingEquiv_itinerary d e ℳ 𝓝 r (σ : Γ →+ Δ)
      σ.injective hr T U hT a v w hv f c ε P W S C k l hcut hpos Q hinj β
  · rw [coefficientEquiv_apply, coefficientMap]
    rw [cutoffDecoratedRayFiberEquiv_apply_val d ℳ T a v f c ε P W S C k Q β,
      cutoffDecoratedRayFiberEquiv_apply_val e 𝓝 U a' w f c ε P W S C l Q]
    exact cutoffDecoratedRayRegradingEmbeddingEquiv_history d e ℳ 𝓝 r (σ : Γ →+ Δ)
      σ.injective hr T U hT a v w hv f c ε P W S C k l hcut hpos Q hinj β

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
