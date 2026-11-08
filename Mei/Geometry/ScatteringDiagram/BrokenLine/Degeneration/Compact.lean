/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Basic
public import Mathlib.Topology.Sequences

/-!
# Compact endpoint families of decorated rays

Over a compact endpoint set the closed full cutoff family is compact in the
compact-open topology on paths. Every sequence of actual decorated rays has a
subsequence with one fixed complete decorated type, convergent endpoints, and
convergent geometric paths. The limiting finite affine ray retains its incoming
direction and the whole type's decoration; a polyhedral incoming source persists.

The endpoint construction follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
A boundary limit is not asserted to be admissible: encounter times may collapse
and singular sets may be met. Equal geometric limits do not identify types.
-/

public noncomputable section

open Set Filter Topology

namespace Mei

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)

/-- Closing the endpoint domains of every complete type gives a compact family
of paths over any compact endpoint set, as a finite union of type-indexed images. -/
theorem isCompact_cutoffDecoratedRay_closedFamily {B : Set V} (hB : IsCompact B) :
    IsCompact (⋃ t : CutoffDecoratedType d ℳ T a v f ε k,
      t.path c '' (B ∩ closure (CutoffDecoratedType.domain c P W S C t))) :=
  isCompact_iUnion fun t => (hB.inter_right isClosed_closure).image (t.path c).continuous

/-- Any sequence in the full cutoff family with compactly confined endpoints
has a subsequence of one complete type. Endpoints and paths converge together,
and the entire final decoration remains constant along this subsequence. -/
theorem CutoffDecoratedRay.exists_type_tendsto_subseq {B : Set V} (hB : IsCompact B)
    {Q : ℕ → V} (hQ : ∀ n, Q n ∈ B)
    (r : ∀ n, CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Q n)) :
    ∃ (t : CutoffDecoratedType d ℳ T a v f ε k) (q : V) (φ : ℕ → ℕ),
      q ∈ B ∩ closure (CutoffDecoratedType.domain c P W S C t) ∧ StrictMono φ ∧
      (∀ n, (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k
        (Q (φ n)) (r (φ n))).val = t) ∧
      (∀ n, (r (φ n)).decoration = t.decoration) ∧
      Tendsto (Q ∘ φ) atTop (𝓝 q) ∧
      Tendsto (fun n => (r (φ n)).realization.2.ray.toContinuousMap)
        atTop (𝓝 (t.path c q)) := by
  let types := fun n =>
    (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k (Q n) (r n)).val
  have hfreq : ∃ᶠ n in atTop, ∃ t, types n = t :=
    (Eventually.of_forall fun n => ⟨types n, rfl⟩).frequently
  obtain ⟨t, ht⟩ := frequently_exists.mp hfreq
  obtain ⟨ψ, hψ, htψ⟩ := extraction_of_frequently_atTop ht
  obtain ⟨q, hqB, η, hη, hq⟩ := hB.tendsto_subseq (fun n => hQ (ψ n))
  let φ := ψ ∘ η
  have htφ : ∀ n, types (φ n) = t := fun n => htψ (η n)
  have hdom : ∀ n, Q (φ n) ∈ CutoffDecoratedType.domain c P W S C t := by
    intro n
    have hh := (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k
      (Q (φ n)) (r (φ n))).property
    exact congrArg (CutoffDecoratedType.domain c P W S C) (htφ n) ▸ hh
  have hq' : Tendsto (Q ∘ φ) atTop (𝓝 q) := hq
  refine ⟨t, q, φ, ⟨hqB, isClosed_closure.mem_of_tendsto hq'
    (Eventually.of_forall fun n => subset_closure (hdom n))⟩, hψ.comp hη,
    htφ, ?_, hq', ?_⟩
  · intro n
    rw [← cutoffDecoratedRayFiberEquiv_decoration d ℳ T a v f c ε P W S C]
    exact congrArg CutoffDecoratedType.decoration (htφ n)
  · have hp := (t.path c).continuous.tendsto q |>.comp hq'
    convert hp using 1
    funext n
    rw [(r (φ n)).toContinuousMap_eq_typePath c P W S C]
    exact congrArg (fun u : CutoffDecoratedType d ℳ T a v f ε k =>
      u.path c (Q (φ n))) (htφ n)

/-- Compact endpoint confinement also supplies an actual limiting affine ray
on the entire negative half-line, with unchanged incoming direction and source.
The complete type and final decoration survive even if encounters collapse. -/
theorem CutoffDecoratedRay.exists_limitRay_tendsto_subseq
    {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
    (hC : IsRationalNormalPolyhedron h C) {B : Set V} (hB : IsCompact B)
    {Q : ℕ → V} (hQ : ∀ n, Q n ∈ B)
    (r : ∀ n, CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Q n)) :
    ∃ (t : CutoffDecoratedType d ℳ T a v f ε k) (q : V) (φ : ℕ → ℕ)
      (β : FiniteAffineRay V V),
      q ∈ B ∩ closure (CutoffDecoratedType.domain c P W S C t) ∧ StrictMono φ ∧
      (∀ n, (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k
        (Q (φ n)) (r (φ n))).val = t) ∧
      (∀ n, (r (φ n)).decoration = t.decoration) ∧
      Tendsto (Q ∘ φ) atTop (𝓝 q) ∧
      Tendsto (fun n => (r (φ n)).realization.2.ray.toContinuousMap)
        atTop (𝓝 (t.path c q)) ∧
      β.endpoint = q ∧ β.incomingDirection = v 0 ∧
      (∀ s : ℝ, s ≤ 0 → β s = t.path c q s) ∧
      ∀ᶠ s : ℝ in atBot, β s ∈ C := by
  obtain ⟨t, q, φ, hq, hφ, ht, hd, hend, hp⟩ :=
    CutoffDecoratedRay.exists_type_tendsto_subseq c P W S C hB hQ r
  obtain ⟨β, hβq, hβv, hβ⟩ := t.exists_limitRay c P W S C hq.2
  refine ⟨t, q, φ, β, hq, hφ, ht, hd, hend, hp, hβq, hβv, hβ, ?_⟩
  filter_upwards [t.path_eventually_mem c P W S C hC hq.2,
    eventually_le_atBot (0 : ℝ)] with s hs hle
  rwa [hβ s hle]

end Mei
