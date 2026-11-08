/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Regrading.Coefficient

/-!
# Identity and composition laws for coefficient embeddings of decorated rays

An injective intertwining coefficient map together with an injective degree map
identifies the actual decorated rays of an input with those of its image, for a fixed
signed encounter itinerary, for all finite itineraries at corresponding cutoffs, and for
complete decorated types. The identity coefficient map induces the identity bijection,
and the bijection induced by a composite of coefficient maps is the composite of the
bijections.

Each comparison is determined by the degree map on the recorded history, because a
decorated ray is determined by its itinerary and degree history. The laws therefore reduce
to the corresponding laws for the degree maps, and no property of the geometric data is
used. The composite statements use the literal composites of the coefficient maps, degree
maps and compatibility proofs, so that the endpoints of the three bijections agree after
unfolding the regraded incoming coefficient `regradeBase`.

The whole-component decorations follow Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2), and Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Definition 2.10 and
Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

open Mei.Convex

section FixedItinerary

variable {R M₁ M₂ M₃ Γ Δ Θ V J K : Type*} [Semiring R]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃] [DecidableEq Γ] [DecidableEq Δ] [DecidableEq Θ]
  (ℳ₁ : Γ → Submodule R M₁) [DirectSum.Decomposition ℳ₁]
  (ℳ₂ : Δ → Submodule R M₂) [DirectSum.Decomposition ℳ₂]
  (ℳ₃ : Θ → Submodule R M₃) [DirectSum.Decomposition ℳ₃]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
  (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (ε : Fin n → SignType)
  (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

/-- The identity coefficient comparison of rays with a fixed itinerary is the identity. -/
theorem decoratedRayCoefficientEmbeddingEquiv_refl {T : Fin n → Module.End R M₁}
    (p₀ : Γ) (a : ℳ₁ p₀) (v : Γ → V) :
    decoratedRayCoefficientEmbeddingEquiv ℳ₁ ℳ₁ LinearMap.id id (fun _ _ hx => hx)
        Function.injective_id T T
        (fun _ => (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm)
        p₀ a v v (fun _ => rfl) f c ε P W S C Q Function.injective_id =
      Equiv.refl _ :=
  Equiv.ext fun _ => DecoratedAdmissibleRay.ext_history
    (decoratedRayCoefficientEmbeddingEquiv_history ..)

/-- Coefficient comparisons of rays with a fixed itinerary compose: the comparison for
a composite of intertwining injective coefficient maps along composite injective degree
maps is the composite of the comparisons. -/
theorem decoratedRayCoefficientEmbeddingEquiv_trans
    (r₁ : M₁ →ₗ[R] M₂) (r₂ : M₂ →ₗ[R] M₃) (σ₁ : Γ → Δ) (σ₂ : Δ → Θ)
    (hr₁ : ∀ p x, x ∈ ℳ₁ p → r₁ x ∈ ℳ₂ (σ₁ p))
    (hr₂ : ∀ p x, x ∈ ℳ₂ p → r₂ x ∈ ℳ₃ (σ₂ p))
    (hσ₁ : Function.Injective σ₁) (hσ₂ : Function.Injective σ₂)
    (hinj₁ : Function.Injective r₁) (hinj₂ : Function.Injective r₂)
    (T₁ : Fin n → Module.End R M₁) (T₂ : Fin n → Module.End R M₂)
    (T₃ : Fin n → Module.End R M₃)
    (hT₁ : ∀ j, r₁.comp (T₁ j) = (T₂ j).comp r₁)
    (hT₂ : ∀ j, r₂.comp (T₂ j) = (T₃ j).comp r₂)
    (p₀ : Γ) (a : ℳ₁ p₀) (v₁ : Γ → V) (v₂ : Δ → V) (v₃ : Θ → V)
    (hv₁ : ∀ p, v₁ p = v₂ (σ₁ p)) (hv₂ : ∀ p, v₂ p = v₃ (σ₂ p)) :
    (decoratedRayCoefficientEmbeddingEquiv ℳ₁ ℳ₂ r₁ σ₁ hr₁ hσ₁ T₁ T₂ hT₁ p₀ a v₁ v₂ hv₁
        f c ε P W S C Q hinj₁).trans
      (decoratedRayCoefficientEmbeddingEquiv ℳ₂ ℳ₃ r₂ σ₂ hr₂ hσ₂ T₂ T₃ hT₂ (σ₁ p₀)
        ⟨r₁ a, hr₁ p₀ a a.property⟩ v₂ v₃ hv₂ f c ε P W S C Q hinj₂) =
    decoratedRayCoefficientEmbeddingEquiv ℳ₁ ℳ₃ (r₂ ∘ₗ r₁) (σ₂ ∘ σ₁)
      (fun p x hx => hr₂ _ _ (hr₁ p x hx)) (hσ₂.comp hσ₁) T₁ T₃
      (fun j => by
        rw [LinearMap.comp_assoc, hT₁ j, ← LinearMap.comp_assoc, hT₂ j, LinearMap.comp_assoc])
      p₀ a v₁ v₃ (fun p => (hv₁ p).trans (hv₂ _)) f c ε P W S C Q (hinj₂.comp hinj₁) :=
  Equiv.ext fun β => DecoratedAdmissibleRay.ext_history (by
    rw [Equiv.trans_apply, decoratedRayCoefficientEmbeddingEquiv_history,
      decoratedRayCoefficientEmbeddingEquiv_history,
      decoratedRayCoefficientEmbeddingEquiv_history]
    rfl)

end FixedItinerary

section Cutoff

variable {R M₁ M₂ M₃ Γ₁ Γ₂ Γ₃ V J I K : Type*} [Semiring R]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]
  [AddCommGroup Γ₁] [DecidableEq Γ₁] [AddCommGroup Γ₂] [DecidableEq Γ₂]
  [AddCommGroup Γ₃] [DecidableEq Γ₃]
  (d₁ : PositiveDegrees Γ₁) (d₂ : PositiveDegrees Γ₂) (d₃ : PositiveDegrees Γ₃)
  (ℳ₁ : Γ₁ → Submodule R M₁) [DirectSum.Decomposition ℳ₁]
  (ℳ₂ : Γ₂ → Submodule R M₂) [DirectSum.Decomposition ℳ₂]
  (ℳ₃ : Γ₃ → Submodule R M₃) [DirectSum.Decomposition ℳ₃]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V) (Q : V)

/-- The identity coefficient comparison of cutoff rays over all itineraries is the
identity. -/
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_refl (T : J → Module.End R M₁)
    (a : ℳ₁ 0) (v : Γ₁ → V) (k : ℕ) :
    cutoffDecoratedRayRegradingEmbeddingEquiv d₁ d₁ ℳ₁ ℳ₁ LinearMap.id (AddMonoidHom.id Γ₁)
        Function.injective_id (fun _ _ hx => hx) T T
        (fun _ => (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm) a v v
        (fun _ => rfl) f c ε P W S C k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q
        Function.injective_id =
      Equiv.refl _ :=
  Equiv.ext fun _ => CutoffDecoratedRay.degreeItinerary_injective (by
    rw [cutoffDecoratedRayRegradingEmbeddingEquiv_degreeItinerary]
    simp only [AddMonoidHom.coe_id, Prod.map_id, List.map_id]
    -- `Equiv.refl` applies as the identity, which the simp set cannot see through the
    -- coefficient `regradeBase` of the target.
    rfl)

/-- Coefficient comparisons of cutoff rays over all itineraries compose. -/
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_trans
    (r₁ : M₁ →ₗ[R] M₂) (r₂ : M₂ →ₗ[R] M₃) (σ₁ : Γ₁ →+ Γ₂) (σ₂ : Γ₂ →+ Γ₃)
    (hσ₁ : Function.Injective σ₁) (hσ₂ : Function.Injective σ₂)
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
    (cutoffDecoratedRayRegradingEmbeddingEquiv d₁ d₂ ℳ₁ ℳ₂ r₁ σ₁ hσ₁ hr₁ T₁ T₂ hT₁ a v₁ v₂
        hv₁ f c ε P W S C k l hcut₁ hpos₁ Q hinj₁).trans
      (cutoffDecoratedRayRegradingEmbeddingEquiv d₂ d₃ ℳ₂ ℳ₃ r₂ σ₂ hσ₂ hr₂ T₂ T₃ hT₂
        (regradeBase ℳ₁ ℳ₂ r₁ σ₁ hr₁ a) v₂ v₃ hv₂ f c ε P W S C l m hcut₂ hpos₂ Q hinj₂) =
    cutoffDecoratedRayRegradingEmbeddingEquiv d₁ d₃ ℳ₁ ℳ₃ (r₂ ∘ₗ r₁) (σ₂.comp σ₁)
      (hσ₂.comp hσ₁) (fun p x hx => hr₂ _ _ (hr₁ p x hx)) T₁ T₃
      (fun j => by
        rw [LinearMap.comp_assoc, hT₁ j, ← LinearMap.comp_assoc, hT₂ j, LinearMap.comp_assoc])
      a v₁ v₃ (fun p => (hv₁ p).trans (hv₂ _)) f c ε P W S C k m
      (fun p => (hcut₁ p).trans (hcut₂ _)) (fun p => (hpos₁ p).trans (hpos₂ _)) Q
      (hinj₂.comp hinj₁) := by
  refine Equiv.ext fun β => CutoffDecoratedRay.degreeItinerary_injective ?_
  refine Eq.trans ?_
    (cutoffDecoratedRayRegradingEmbeddingEquiv_degreeItinerary d₁ d₃ ℳ₁ ℳ₃ (r₂ ∘ₗ r₁)
      (σ₂.comp σ₁) (hσ₂.comp hσ₁) _ T₁ T₃ _ a v₁ v₃ _ f c ε P W S C k m _ _ Q
      (hinj₂.comp hinj₁) β).symm
  rw [Equiv.trans_apply, cutoffDecoratedRayRegradingEmbeddingEquiv_degreeItinerary,
    cutoffDecoratedRayRegradingEmbeddingEquiv_degreeItinerary, List.map_map]
  rfl

end Cutoff

section Types

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

omit [AddCommGroup Γ₁] [AddCommGroup Γ₂] [AddCommGroup Γ₃]
  [DecidableEq Γ₁] [DecidableEq Γ₂] [DecidableEq Γ₃] in
private theorem heq_comp_comp {n n' : ℕ} (hn : n = n') {g : Fin n → Γ₂} {g' : Fin n' → Γ₁}
    (σ₂ : Γ₂ → Γ₃) (σ₁ : Γ₁ → Γ₂) (h : HEq g (σ₁ ∘ g')) : HEq (σ₂ ∘ g) (σ₂ ∘ σ₁ ∘ g') := by
  subst hn
  exact heq_of_eq (congrArg (σ₂ ∘ ·) (eq_of_heq h))

/-- The identity coefficient comparison of complete decorated types is the identity. -/
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
    exact h₂.trans ((heq_comp_comp (by simp) σ₂ σ₁ h₁).trans h₃.symm)

end Types

end Mei
