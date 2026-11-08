/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Data.Fin.Insertion
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Coefficient.Embedding
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Deletion
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Insertion

/-!
# Coefficient comparisons and artificial subdivisions of decorated rays

Restoring an identity encounter inside a straight segment of a decorated ray, or deleting
an encounter that fixes the whole decoration, does not change the broken line it describes.
The coefficient comparison `decoratedRayCoefficientEquiv` commutes with both operations.

For restoration (`decoratedRayCoefficientEquiv_insertIdentityEncounter`), the comparison for
the subdivided itinerary sends the restored source ray to a ray with the history, path, incoming
tail, encounter parameters and segment decorations of the restored image ray. The geometric
conditions for restoring an encounter are the same on the source ray and on its image
(`insertIdentityEncounter_conditions_iff`), so the restoration is available on one side exactly
when it is on the other. For deletion (`decoratedRayCoefficientEquiv_removeEncounter`), the
comparison for the shortened itinerary sends the shortened source ray to the shortened image ray.

No injectivity of the coefficient map is needed, and unchanged-degree encounters and
degree changes of zero spatial direction are retained throughout. The conventions for
artificial subdivisions are those of Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2), and Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Definition 2.10
(arXiv:1503.06183v5).
-/

public section

namespace Mei

open Mei.Convex

section Insertion

variable {R M N Γ Δ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [DecidableEq Γ] [DecidableEq Δ]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ → Δ)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  (hσ : Function.Injective σ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (p₀ : Γ) (a : ℳ p₀) (v : Γ → V) (w : Δ → V)
  (hv : ∀ p, v p = w (σ p))
  (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (ε : Fin n → SignType)
  (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

omit [DecidableEq Γ] [DecidableEq Δ] [NormedAddCommGroup V] [NormedSpace ℝ V] in
include hT in
/-- Inserting the identity at the same position of two itineraries preserves the intertwining
of their propagation maps by a coefficient map. -/
theorem intertwines_insertNth_id (i : Fin (n + 1)) :
    ∀ j, r.comp (i.insertNth (α := fun _ => Module.End R M) LinearMap.id T j) =
      (i.insertNth (α := fun _ => Module.End R N) LinearMap.id U j).comp r := by
  intro j
  cases j using Fin.succAboveCases i <;> simp [hT]

variable (β : {β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q //
      r (β.decoration 0) ≠ 0})
  (ρ : DecoratedAdmissibleRay 𝓝 U (σ p₀) ⟨r a, hr p₀ a a.property⟩ w f c ε P W S C Q)
  (hρ : decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
    f c ε P W S C Q β = ρ)
  (i : Fin (n + 1)) (t : ℝ) (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)

include hσ hv hρ in
/-- The geometric conditions for restoring an identity encounter inside a straight segment
are the same for a decorated ray and for its image under the coefficient comparison: the
path, the encounter parameters and the spatial velocity of every segment agree. -/
theorem insertIdentityEncounter_conditions_iff :
    (m (w (Fin.snoc (α := fun _ => Δ) ρ.1.val (σ p₀) i)) ≠ 0 ∧ m (ρ.2.ray t) = b ∧
      ρ.2.ray t ∈ H ∧ (∀ s, s < 0 → s ≠ t →
        (∀ j : Fin n, s ≠ ρ.2.parameter j.succ) → ρ.2.ray s ∉ H) ∧ Q ∉ H) ↔
    (m (v (Fin.snoc (α := fun _ => Γ) β.val.1.val p₀ i)) ≠ 0 ∧ m (β.val.2.ray t) = b ∧
      β.val.2.ray t ∈ H ∧ (∀ s, s < 0 → s ≠ t →
        (∀ j : Fin n, s ≠ β.val.2.parameter j.succ) → β.val.2.ray s ∉ H) ∧ Q ∉ H) := by
  subst hρ
  have hq : w (Fin.snoc (α := fun _ => Δ)
      (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv f c ε P W S C Q β).1.val
      (σ p₀) i) = v (Fin.snoc (α := fun _ => Γ) β.val.1.val p₀ i) := by
    rw [hv, decoratedRayCoefficientEquiv_history, ← Function.comp_apply (f := σ), Fin.comp_snoc]
  simp only [hq, decoratedRayCoefficientEquiv_ray, decoratedRayCoefficientEquiv_parameter]

variable (hbefore : t < β.val.2.parameter i)
  (hafter : ∀ k, i < k → β.val.2.parameter k < t)
  (htrans : m (v (Fin.snoc (α := fun _ => Γ) β.val.1.val p₀ i)) ≠ 0)
  (hheight : m (β.val.2.ray t) = b) (hinc : β.val.2.ray t ∈ H)
  (havoid : ∀ s, s < 0 → s ≠ t →
    (∀ j : Fin n, s ≠ β.val.2.parameter j.succ) → β.val.2.ray s ∉ H)
  (hoff : Q ∉ H)

include hρ in
/-- The comparison for the subdivided itinerary sends the ray with a restored identity
encounter to the ray with the restored data of the image: the history, the path and
incoming tail, the encounter parameters with the restored time inserted, and the segment
decorations, repeated across the restored encounter, are those of the restored image ray. -/
theorem decoratedRayCoefficientEquiv_insertIdentityEncounter
    (s : DecoratedAdmissibleRay 𝓝 (i.insertNth LinearMap.id U) (σ p₀) ⟨r a, hr p₀ a a.property⟩ w
      (i.insertNth m f) (i.insertNth b c)
      (i.insertNth (SignType.sign (m (v (Fin.snoc (α := fun _ => Γ) β.val.1.val p₀ i)))) ε)
      (i.insertNth H P) (Sum.elim W fun _ : Unit => H) S C Q)
    (hs : decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ (i.insertNth LinearMap.id T)
      (i.insertNth LinearMap.id U) (intertwines_insertNth_id r T U hT i) p₀ a v w hv
      (i.insertNth m f) (i.insertNth b c)
      (i.insertNth (SignType.sign (m (v (Fin.snoc (α := fun _ => Γ) β.val.1.val p₀ i)))) ε)
      (i.insertNth H P) (Sum.elim W fun _ : Unit => H) S C Q
      ⟨β.val.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff,
        by rw [DecoratedAdmissibleRay.decoration_zero_insertIdentityEncounter]
           exact β.property⟩ = s) :
    s.1.val = i.insertNth (α := fun _ => Δ) (Fin.snoc (α := fun _ => Δ) ρ.1.val (σ p₀) i)
        ρ.1.val ∧
      s.2.ray = ρ.2.ray ∧
      s.2.parameter = i.succ.insertNth (α := fun _ => ℝ) t ρ.2.parameter ∧
      ∀ j, s.decoration (i.castSucc.succAbove j) = ρ.decoration j := by
  subst hρ hs
  refine ⟨?_, ?_, ?_, fun j => ?_⟩
  · have hsnoc := congrFun (Fin.comp_snoc σ β.val.1.val p₀) i
    simp only [decoratedRayCoefficientEquiv_history,
      DecoratedAdmissibleRay.history_insertIdentityEncounter, Fin.comp_insertNth,
      Function.comp_apply] at hsnoc ⊢
    rw [hsnoc]
  · simp only [decoratedRayCoefficientEquiv_ray,
      DecoratedAdmissibleRay.ray_insertIdentityEncounter]
  · simp only [decoratedRayCoefficientEquiv_parameter,
      DecoratedAdmissibleRay.parameter_insertIdentityEncounter]
  · simp only [decoratedRayCoefficientEquiv_decoration,
      DecoratedAdmissibleRay.decoration_insertIdentityEncounter]

end Insertion

section Deletion

variable {R M N Γ Δ V J J' K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [DecidableEq Γ] [DecidableEq Δ]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ → Δ)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  (hσ : Function.Injective σ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : Fin (n + 1) → Module.End R M) (U : Fin (n + 1) → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (p₀ : Γ) (a : ℳ p₀) (v : Γ → V) (w : Δ → V)
  (hv : ∀ p, v p = w (σ p))
  (f : Fin (n + 1) → V →L[ℝ] ℝ) (c : Fin (n + 1) → ℝ) (ε : Fin (n + 1) → SignType)
  (P : Fin (n + 1) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)
  (β : {β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q // r (β.decoration 0) ≠ 0})
  (i : Fin (n + 1)) (hfix : β.val.decoration i.castSucc = β.val.decoration i.succ)
  (W' : J' → Set V) (e : J' → J) (hW : ∀ j, W' j ⊆ W (e j))
  (hoff : ∀ j, β.val.2.ray (β.val.2.parameter i.succ) ∉ W' j)

omit [DecidableEq Γ] [DecidableEq Δ] [NormedAddCommGroup V] [NormedSpace ℝ V] in
include hT in
/-- Deleting the same position from two itineraries preserves the intertwining of their
propagation maps by a coefficient map. -/
theorem intertwines_removeNth (i : Fin (n + 1)) :
    ∀ j, r.comp (i.removeNth T j) = (i.removeNth U j).comp r := by
  intro j
  simpa only [Fin.removeNth_apply] using hT (i.succAbove j)

/-- Deleting an encounter that fixes the whole decoration commutes with the coefficient
comparison: the comparison for the shortened itinerary sends the shortened ray to the
shortened image ray. The image ray fixes its decoration at the encounter and its encounter
point misses the retained walls, because the decoration, path and parameters of the image are
those of the source (`decoratedRayCoefficientEquiv_decoration`,
`decoratedRayCoefficientEquiv_ray`, `decoratedRayCoefficientEquiv_parameter`). -/
theorem decoratedRayCoefficientEquiv_removeEncounter :
    decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ (i.removeNth T) (i.removeNth U)
      (intertwines_removeNth r T U hT i) p₀ a v w hv (i.removeNth f) (i.removeNth c)
      (i.removeNth ε) (i.removeNth P) W' S C Q
      ⟨β.val.removeEncounter i hfix W' e hW hoff, by
        rw [DecoratedAdmissibleRay.decoration_zero_removeEncounter]
        exact β.property⟩ =
    (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv f c ε P W S C Q
      β).removeEncounter i
      (by simp only [decoratedRayCoefficientEquiv_decoration, hfix]) W' e hW
      (by simpa only [decoratedRayCoefficientEquiv_ray,
        decoratedRayCoefficientEquiv_parameter] using hoff) := by
  apply DecoratedAdmissibleRay.ext_history
  rw [decoratedRayCoefficientEquiv_history, DecoratedAdmissibleRay.history_removeEncounter,
    DecoratedAdmissibleRay.history_removeEncounter, decoratedRayCoefficientEquiv_history]
  funext j
  simp [Fin.removeNth_apply]

end Deletion

end Mei
