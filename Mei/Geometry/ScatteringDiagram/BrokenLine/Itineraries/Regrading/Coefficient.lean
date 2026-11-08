/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Regrading

/-!
# Coefficient embeddings of complete decorated types

An injective intertwining coefficient map and a degree isomorphism identify
complete cutoff decorated types, including types with empty endpoint domains.
The comparison preserves encounter words, regrades entire histories, and maps
whole final decorations. Endpoint domains are unchanged, and the comparison
agrees with coefficient transport of actual rays.

The construction uses the whole-history coefficient comparison
`map_homogeneousHistory_of_injective`. The interpretation of endpoint domains
follows Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*,
§4 (arXiv:2205.07753v2).
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

section IdentityComposition

variable {R M₁ M₂ M₃ Γ₁ Γ₂ Γ₃ V J : Type*} [Semiring R]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]
  [AddCommGroup Γ₁] [DecidableEq Γ₁] [AddCommGroup Γ₂] [DecidableEq Γ₂]
  [AddCommGroup Γ₃] [DecidableEq Γ₃]
  (d₁ : PositiveDegrees Γ₁) (d₂ : PositiveDegrees Γ₂) (d₃ : PositiveDegrees Γ₃)
  (ℳ₁ : Γ₁ → Submodule R M₁) [DirectSum.Decomposition ℳ₁]
  (ℳ₂ : Γ₂ → Submodule R M₂) [DirectSum.Decomposition ℳ₂]
  (ℳ₃ : Γ₃ → Submodule R M₃) [DirectSum.Decomposition ℳ₃]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (f : J → V →L[ℝ] ℝ) (ε : J → SignType)

/-- The identity coefficient comparison of complete decorated types is the identity. -/
@[simp]
theorem cutoffDecoratedTypeCoefficientEquiv_refl (T : J → Module.End R M₁)
    (a : ℳ₁ 0) (v : Γ₁ → V) (k : ℕ) :
    cutoffDecoratedTypeCoefficientEquiv d₁ d₁ ℳ₁ ℳ₁ LinearMap.id (AddEquiv.refl Γ₁)
        Function.injective_id (fun _ _ hx => hx) T T
        (fun _ => (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm) a v v
        (fun _ => rfl) f ε k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) =
      Equiv.refl _ :=
  Equiv.ext fun _ => CutoffDecoratedType.ext_val
    (cutoffDecoratedTypeCoefficientEquiv_itinerary ..)
    (cutoffDecoratedTypeCoefficientEquiv_history ..)

/-- Coefficient comparisons of complete decorated types compose. -/
@[simp]
theorem cutoffDecoratedTypeCoefficientEquiv_trans
    (r₁ : M₁ →ₗ[R] M₂) (r₂ : M₂ →ₗ[R] M₃) (σ₁ : Γ₁ ≃+ Γ₂) (σ₂ : Γ₂ ≃+ Γ₃)
    (hinj₁ : Function.Injective r₁) (hinj₂ : Function.Injective r₂)
    (hr₁ : ∀ p x, x ∈ ℳ₁ p → r₁ x ∈ ℳ₂ (σ₁ p))
    (hr₂ : ∀ p x, x ∈ ℳ₂ p → r₂ x ∈ ℳ₃ (σ₂ p))
    (T₁ : J → Module.End R M₁) (T₂ : J → Module.End R M₂) (T₃ : J → Module.End R M₃)
    (hT₁ : ∀ j, r₁.comp (T₁ j) = (T₂ j).comp r₁)
    (hT₂ : ∀ j, r₂.comp (T₂ j) = (T₃ j).comp r₂)
    (a : ℳ₁ 0) (v₁ : Γ₁ → V) (v₂ : Γ₂ → V) (v₃ : Γ₃ → V)
    (hv₁ : ∀ p, v₁ p = v₂ (σ₁ p)) (hv₂ : ∀ p, v₂ p = v₃ (σ₂ p)) (k l m : ℕ)
    (hcut₁ : ∀ p, p ∈ d₁.cutoff k ↔ σ₁ p ∈ d₂.cutoff l)
    (hcut₂ : ∀ p, p ∈ d₂.cutoff l ↔ σ₂ p ∈ d₃.cutoff m)
    (hpos₁ : ∀ p, p ∈ d₁.monoid ↔ σ₁ p ∈ d₂.monoid)
    (hpos₂ : ∀ p, p ∈ d₂.monoid ↔ σ₂ p ∈ d₃.monoid) :
    (cutoffDecoratedTypeCoefficientEquiv d₁ d₂ ℳ₁ ℳ₂ r₁ σ₁ hinj₁ hr₁ T₁ T₂ hT₁ a v₁ v₂ hv₁
        f ε k l hcut₁ hpos₁).trans
      (cutoffDecoratedTypeCoefficientEquiv d₂ d₃ ℳ₂ ℳ₃ r₂ σ₂ hinj₂ hr₂ T₂ T₃ hT₂
        (regradeBase ℳ₁ ℳ₂ r₁ (σ₁ : Γ₁ →+ Γ₂) hr₁ a) v₂ v₃ hv₂ f ε l m hcut₂ hpos₂) =
    cutoffDecoratedTypeCoefficientEquiv d₁ d₃ ℳ₁ ℳ₃ (r₂ ∘ₗ r₁) (σ₁.trans σ₂)
      (hinj₂.comp hinj₁) (fun p x hx => hr₂ _ _ (hr₁ p x hx)) T₁ T₃
      (fun j => by
        rw [LinearMap.comp_assoc, hT₁ j, ← LinearMap.comp_assoc, hT₂ j, LinearMap.comp_assoc])
      a v₁ v₃ (fun p => (hv₁ p).trans (hv₂ _)) f ε k m
      (fun p => (hcut₁ p).trans (hcut₂ _)) (fun p => (hpos₁ p).trans (hpos₂ _)) := by
  have hT₃ : ∀ j, (r₂ ∘ₗ r₁).comp (T₁ j) = (T₃ j).comp (r₂ ∘ₗ r₁) := fun j => by
    rw [LinearMap.comp_assoc, hT₁ j, ← LinearMap.comp_assoc, hT₂ j, LinearMap.comp_assoc]
  refine Equiv.ext fun t => CutoffDecoratedType.ext_val ?_ ?_
  · have h₁ := cutoffDecoratedTypeCoefficientEquiv_itinerary d₁ d₂ ℳ₁ ℳ₂ r₁ σ₁ hinj₁ hr₁ T₁ T₂
      hT₁ a v₁ v₂ hv₁ f ε k l hcut₁ hpos₁ t
    have h₂ := cutoffDecoratedTypeCoefficientEquiv_itinerary d₂ d₃ ℳ₂ ℳ₃ r₂ σ₂ hinj₂ hr₂ T₂ T₃
      hT₂ (regradeBase ℳ₁ ℳ₂ r₁ (σ₁ : Γ₁ →+ Γ₂) hr₁ a) v₂ v₃ hv₂ f ε l m hcut₂ hpos₂
      (cutoffDecoratedTypeCoefficientEquiv d₁ d₂ ℳ₁ ℳ₂ r₁ σ₁ hinj₁ hr₁ T₁ T₂ hT₁ a v₁ v₂
        hv₁ f ε k l hcut₁ hpos₁ t)
    have h₃ := cutoffDecoratedTypeCoefficientEquiv_itinerary d₁ d₃ ℳ₁ ℳ₃ (r₂ ∘ₗ r₁)
      (σ₁.trans σ₂) (hinj₂.comp hinj₁) (fun p x hx => hr₂ _ _ (hr₁ p x hx)) T₁ T₃ hT₃ a v₁ v₃
      (fun p => (hv₁ p).trans (hv₂ _)) f ε k m (fun p => (hcut₁ p).trans (hcut₂ _))
      (fun p => (hpos₁ p).trans (hpos₂ _)) t
    rw [Equiv.trans_apply]
    exact h₂.trans (h₁.trans h₃.symm)
  · rw [Equiv.trans_apply]
    have h₁ := cutoffDecoratedTypeCoefficientEquiv_history d₁ d₂ ℳ₁ ℳ₂ r₁ σ₁ hinj₁ hr₁ T₁ T₂
      hT₁ a v₁ v₂ hv₁ f ε k l hcut₁ hpos₁ t
    have h₂ := cutoffDecoratedTypeCoefficientEquiv_history d₂ d₃ ℳ₂ ℳ₃ r₂ σ₂ hinj₂ hr₂ T₂ T₃
      hT₂ (regradeBase ℳ₁ ℳ₂ r₁ (σ₁ : Γ₁ →+ Γ₂) hr₁ a) v₂ v₃ hv₂ f ε l m hcut₂ hpos₂
      (cutoffDecoratedTypeCoefficientEquiv d₁ d₂ ℳ₁ ℳ₂ r₁ σ₁ hinj₁ hr₁ T₁ T₂ hT₁ a v₁ v₂
        hv₁ f ε k l hcut₁ hpos₁ t)
    have h₃ := cutoffDecoratedTypeCoefficientEquiv_history d₁ d₃ ℳ₁ ℳ₃ (r₂ ∘ₗ r₁)
      (σ₁.trans σ₂) (hinj₂.comp hinj₁) (fun p x hx => hr₂ _ _ (hr₁ p x hx)) T₁ T₃ hT₃ a v₁ v₃
      (fun p => (hv₁ p).trans (hv₂ _)) f ε k m (fun p => (hcut₁ p).trans (hcut₂ _))
      (fun p => (hpos₁ p).trans (hpos₂ _)) t
    have hcomp := congr((fun {n : ℕ} (g : Fin n → Γ₂) => σ₂ ∘ g) $h₁)
    exact h₂.trans (((heq_of_eq hcomp).trans h₃.symm))

end IdentityComposition

end Mei
