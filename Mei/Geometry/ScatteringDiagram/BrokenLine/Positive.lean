/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Map
public import Mei.LinearAlgebra.GradedModule.History.Positive

/-!
# Positive decorated-ray evaluations

Admissible component maps preserving chosen additive positive monoids give positive whole
segment decorations and positive components of finite weighted evaluations.
Both a fixed signed itinerary and the full family of cutoff itineraries are
covered. Geometric admissibility only selects histories; it cannot introduce
negative coefficients. Coincident paths with different histories retain their
multiplicities, and no endpoint genericity or noncancellation assumption is used.
Positivity is required only on pairs of degrees with the prescribed crossing sign
and preserved normal velocity, so a signed action may fail to be positive elsewhere.

Degree-preserving coefficient maps preserving these monoids also preserve the
conclusion for the actual target evaluation, even when specialization kills
some source decorations. This uses `map_cutoffDecoratedEvaluation` and the
componentwise positivity of `homogeneousHistoryStage`.

For the positivity argument by whole homogeneous decorations, see
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definition 3.1 and Theorem 1.13 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (Pos : Γ → AddSubmonoid M)
  [NormedAddCommGroup V] [NormedSpace ℝ V]

section FixedItinerary

variable {n : ℕ} (T : Fin n → Module.End R M)
  (p₀ : Γ) (a : ℳ p₀) (ha : (a : M) ∈ Pos p₀)
  (v : Γ → V) (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (ε : Fin n → SignType) (P : Fin n → Set V)
  (W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

variable (hT : ∀ j p q, f j (v q) = f j (v p) →
    SignType.sign (f j (v q)) = ε j → ∀ x, x ∈ ℳ p → x ∈ Pos p →
      (DirectSum.decompose ℳ (T j x) q : M) ∈ Pos q)

include hT ha

/-- Every homogeneous component of the weighted fiber sum is positive.
The sum uses actual admissible rays, including their full avoidance and source
conditions, rather than all syntactically possible histories. -/
theorem decoratedRayEvaluation_component_mem_addSubmonoid (q : Γ) :
    (DirectSum.decompose ℳ
      (decoratedRayEvaluation ℳ T p₀ a v f c ε P W S C Q) q : M) ∈ Pos q := by
  classical
  rw [decoratedRayEvaluation_eq_sum]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  apply (Pos q).sum_mem
  intro p _
  split_ifs
  · have hp := (mem_decoratedHistorySupport ..).mp p.property
    exact homogeneousHistory_component_mem_addSubmonoid ℳ Pos T p.val
      (fun j => hT j _ _ (hp.2 j).1 (hp.2 j).2) a ha q
  · simp only [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
    exact (Pos q).zero_mem

end FixedItinerary

section Cutoff

variable [AddCommGroup Γ] (d : PositiveDegrees Γ) (T : J → Module.End R M)
  (a : ℳ 0) (ha : (a : M) ∈ Pos 0)
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V) (k : ℕ) (Q : V)

variable (hT : ∀ j p q, f j (v q) = f j (v p) →
    SignType.sign (f j (v q)) = ε j → ∀ x, x ∈ ℳ p → x ∈ Pos p →
      (DirectSum.decompose ℳ (T j x) q : M) ∈ Pos q)

include hT ha

/-- Positive component propagation and a positive incoming coefficient give
positive homogeneous components of the full weighted evaluation over all
cutoff itineraries. Every endpoint is permitted. -/
theorem cutoffDecoratedEvaluation_component_mem_addSubmonoid [Finite J] (q : Γ) :
    (DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) ∈ Pos q := by
  classical
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  rw [cutoffDecoratedEvaluation_def]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  apply (Pos q).sum_mem
  intro r _
  rw [CutoffDecoratedRay.decoration_eq]
  have hp := (mem_decoratedHistorySupport ..).mp r.realization.1.property
  exact homogeneousHistory_component_mem_addSubmonoid ℳ Pos _ r.realization.1.val
    (fun j => hT (r.itinerary.get j) _ _ (hp.2 j).1 (hp.2 j).2) a ha q

end Cutoff

section CoefficientMap

variable {N : Type*} [AddCommMonoid N] [Module R N] [AddCommGroup Γ]
  (d : PositiveDegrees Γ) (𝓝 : Γ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (Pos' : Γ → AddSubmonoid N) (r : M →ₗ[R] N)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 p)
  (hPos : ∀ p x, x ∈ ℳ p → x ∈ Pos p → r x ∈ Pos' p)
  (T : J → Module.End R M) (U : J → Module.End R N)
  (hTU : ∀ j, r.comp (T j) = (U j).comp r)
  (a : ℳ 0) (ha : (a : M) ∈ Pos 0)
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V) (k : ℕ) (Q : V)

variable (hT : ∀ j p q, f j (v q) = f j (v p) →
    SignType.sign (f j (v q)) = ε j → ∀ x, x ∈ ℳ p → x ∈ Pos p →
      (DirectSum.decompose ℳ (T j x) q : M) ∈ Pos q)

include hPos hT hTU ha

/-- A positive coefficient map sends the entire evaluation to a positive target
evaluation. It need not be injective, and the target propagation need only
intertwine the source maps; positivity away from their images is not required. -/
theorem cutoffDecoratedEvaluation_component_mem_addSubmonoid_of_map [Finite J] (q : Γ) :
    (DirectSum.decompose 𝓝
      (cutoffDecoratedEvaluation d 𝓝 U ⟨r a, hr 0 a a.property⟩
        v f c ε P W S C k Q) q : N) ∈ Pos' q := by
  rw [← map_cutoffDecoratedEvaluation d ℳ 𝓝 r hr T U hTU a v f c ε P W S C k Q]
  have he := DirectSum.map_decompose_shift ℳ 𝓝 r.toAddMonoidHom id
    Function.injective_id hr q
    (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q)
  simp only [LinearMap.toAddMonoidHom_coe, id_eq] at he
  rw [← he]
  exact hPos q _ (DirectSum.decompose ℳ _ q).property
    (cutoffDecoratedEvaluation_component_mem_addSubmonoid ℳ Pos d T
      a ha v f c ε P W S C k Q hT q)

end CoefficientMap

end Mei
