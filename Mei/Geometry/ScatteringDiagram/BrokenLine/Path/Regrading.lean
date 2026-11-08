/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Linear

/-!
# Weighted regrading of rays through varying chambers

Vertexwise coefficient maps intertwining transfers commute with actual weighted
ray evaluations when their degree maps preserve spatial velocities. Degree maps
may merge infinitely many degrees, and coefficient maps may kill decorations.
The images of source histories are added before zero target histories are
removed. Thus the comparison is an equality of weighted sums rather than a
bijection of rays. Every surviving target ray nevertheless has a surviving
source refinement with the same whole path and encounter parameters.

The linear comparison holds on the entire incoming homogeneous piece without
global finite grading support or finite generation. Geometric selection retains
all signed encounters, unrecorded-wall and singular avoidance, and the original
incoming tail. It factors through `Quiver.Path.map_sum_ite_homogeneousHistory`,
the shared finite component expansion for independently graded chamber modules.
Whole-component propagation follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M N : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  {ι κ : Q → Type*} [∀ q, DecidableEq (ι q)] [∀ q, DecidableEq (κ q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (U : ∀ {b c : Q}, (b ⟶ c) → N b →ₗ[R] N c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  (𝓝 : ∀ q, κ q → Submodule R (N q)) [∀ q, DirectSum.Decomposition (𝓝 q)]
  (r : ∀ q, M q →ₗ[R] N q) (σ : ∀ q, ι q → κ q)
  (hr : ∀ q d x, x ∈ ℳ q d → r q x ∈ 𝓝 q (σ q d))
  (hT : ∀ {b c : Q} (e : b ⟶ c), (r c).comp (T e) = (U e).comp (r b))
  {a b : Q} (i₀ : ι a)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V) (w : ∀ q, κ q → V)
  (hv : ∀ q d, w q (σ q d) = v q d)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "dirs(" p ", " d ")" => Path.Degrees.reverseVertexLabels v i₀ p d
local notation "tdirs(" p ", " d ")" => Path.Degrees.reverseVertexLabels w (σ a i₀) p d
local notation "normals(" p ")" => Path.reverseArrowLabels ν p

include hT hv

/-- Weighted evaluation commutes with arbitrary velocity-preserving regrading.
Histories with a common image are grouped, including groups that cancel to zero;
no injectivity, finite degree fibers or endpoint genericity is assumed. -/
theorem map_pathDecoratedEvaluation (x : ℳ a i₀) (s : Finset (Path a b)) (X : V) :
    r b (pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X) =
      pathDecoratedEvaluation U 𝓝 (σ a i₀) ⟨r a x, hr a i₀ x x.property⟩
        s w ν ε c P W S C X := by
  classical
  rw [pathDecoratedEvaluation_eq_sum_homogeneousHistory,
    pathDecoratedEvaluation_eq_sum_homogeneousHistory, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  let E (d : p.val.Degrees κ) : Prop :=
    (∀ j, normals(p.val) j (tdirs(p.val, d) (Fin.castSucc j)) =
        normals(p.val) j (tdirs(p.val, d) (Fin.succ j)) ∧
      SignType.sign (normals(p.val) j (tdirs(p.val, d) (Fin.castSucc j))) =
        Path.reverseArrowLabels ε p.val j) ∧
    X ∈ admissibleBackwardDomain normals(p.val) (Path.reverseArrowLabels c p.val)
      tdirs(p.val, d) (Path.reverseArrowLabels P p.val) W S C
  have he := p.val.map_sum_ite_homogeneousHistory T ℳ U 𝓝 r σ (fun _ => hr _) hT E x
  -- The geometric tests are the same after replacing every segment velocity;
  -- comparing summands also reconciles their independent decidability instances.
  convert he using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro d _
    simp only [E, Path.Degrees.reverseVertexLabels_map σ v w hv]
  · apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl

/-- The comparison is an identity of linear operators on the whole incoming
piece, with no uniform finite support assumption on that piece. -/
theorem map_pathDecoratedEvaluationLinearMap (s : Finset (Path a b)) (X : V) :
    (r b).comp (pathDecoratedEvaluationLinearMap T ℳ i₀ s v ν ε c P W S C X) =
      (pathDecoratedEvaluationLinearMap U 𝓝 (σ a i₀) s w ν ε c P W S C X).comp
        ((r a).restrict (hr a i₀)) := by
  ext x
  simpa only [LinearMap.comp_apply, pathDecoratedEvaluationLinearMap_apply,
    LinearMap.restrict_apply] using
    map_pathDecoratedEvaluation T U ℳ 𝓝 r σ hr hT i₀ v w hv ν ε c P W S C x s X

/-- Every surviving target ray has a source refinement whose whole final
coefficient survives. The complete path, incoming tail and encounter parameters
are identical. Individual source rays need not survive grouping in the target. -/
theorem PathDecoratedRay.exists_coefficient_refinement (x : ℳ a i₀) (p : Path a b) (X : V)
    (β : PathDecoratedRay U 𝓝 (σ a i₀) ⟨r a x, hr a i₀ x x.property⟩
      w ν ε c P W S C p X) :
    ∃ α : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X,
      Path.Degrees.map σ p α.1.val = β.1.val ∧ r b α.decoration ≠ 0 ∧
        α.2.ray = β.2.ray ∧ α.2.parameter = β.2.parameter := by
  have hβ : p.homogeneousHistory U 𝓝 β.1.val (r a x) ≠ 0 := by
    simpa only [PathDecoratedRay.decoration_def] using β.decoration_ne_zero
  obtain ⟨d, hd, hn⟩ := p.exists_homogeneousHistory_ne_zero_of_map_ne_zero
    T ℳ U 𝓝 r σ (fun _ => hr _) hT β.1.val hβ
  have hdir : tdirs(p, β.1.val) = dirs(p, d) := by
    rw [← hd, Path.Degrees.reverseVertexLabels_map σ v w hv]
  have hnorm := ((mem_pathDecoratedHistorySupport U 𝓝 (σ a i₀)
    ⟨r a x, hr a i₀ x x.property⟩ w ν ε p β.1.val).mp β.1.property).2
  have hs : d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p := by
    rw [mem_pathDecoratedHistorySupport]
    exact ⟨fun hz => hn (by rw [hz, map_zero]), by simpa only [hdir] using hnorm⟩
  refine ⟨⟨⟨d, hs⟩, β.2.congrVelocity hdir⟩, hd, ?_, ?_, ?_⟩
  · simpa only [PathDecoratedRay.decoration_def] using hn
  · exact AdmissibleRayRealization.ray_congrVelocity ..
  · exact AdmissibleRayRealization.parameter_congrVelocity ..

end Mei
