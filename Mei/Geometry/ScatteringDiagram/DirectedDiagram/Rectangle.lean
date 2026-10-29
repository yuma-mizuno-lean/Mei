/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Geometry.Affine.IncomingGerm

/-!
# Comparing crossings along a common tangent direction

In a consistent directed diagram, regular crossing labels agree after displacement
parallel to every active wall, provided the crossing line misses the affine spans
of walls parallel to that line. Short transverse crossings bound a parallelogram
whose other two sides meet no wall. Consistency therefore equates the crossings,
even if the intervening segment inside the wall slice meets singular support.

This uses `AffineSubspace.eventually_smul_vadd_notMem`, the short crossing
construction in `DirectedDiagram.LocalCrossing`, and endpoint independence of
`DirectedDiagram.levelPathProduct`. The parallelogram argument for module probes
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- A displacement tangent to all active walls preserves regular combined
crossing labels in a consistent diagram. The crossing line must miss the affine
span of each wall to which it is parallel. No regularity along the displacement
segment itself is required. -/
theorem combinedLabel_eq_of_parallel_displacement (k : ℕ) (hD : D.LevelConsistent k)
    (θ v w : V)
    (hθ : θ ∉ singularSupport (fun a : D.active k => (D.wall a).support))
    (hη : θ + w ∉ singularSupport (fun a : D.active k => (D.wall a).support))
    (hw : ∀ a : D.active k, h.realCharacter (D.wall a).normal w = 0)
    (hparallel : ∀ a : D.active k, h.realCharacter (D.wall a).normal v = 0 →
      θ ∉ affineSpan ℝ (D.wall a).support) :
    D.combinedLabel k (θ + w) v hη = D.combinedLabel k θ v hθ := by
  classical
  have hwd (a : D.active k) : w ∈ (affineSpan ℝ (D.wall a).support).direction := by
    rw [(D.wall a).direction_support, LinearMap.mem_ker]
    exact hw a
  have htrans (a : D.active k) (ha : θ ∈ (D.wall a).support) :
      h.realCharacter (D.wall a).normal v ≠ 0 :=
    fun hv => hparallel a hv (subset_affineSpan ℝ _ ha)
  have htrans' (a : D.active k) (ha : θ + w ∈ (D.wall a).support) :
      h.realCharacter (D.wall a).normal v ≠ 0 := by
    intro hv
    apply hparallel a hv
    have he := (affineSpan ℝ (D.wall a).support).vadd_mem_iff_mem_of_mem_direction (hwd a)
      (p := θ)
    exact he.mp (by simpa [add_comm] using subset_affineSpan ℝ _ ha)
  -- Offset the two long sides away from every active supporting hyperplane.
  have hmiss : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ b : D.active k,
      θ - a • v ∉ affineSpan ℝ (D.wall b).support ∧
      θ + a • v ∉ affineSpan ℝ (D.wall b).support := by
    apply eventually_all.mpr
    intro b
    let S := affineSpan ℝ (D.wall b).support
    by_cases hv : v ∈ S.direction
    · have hnot := hparallel b (by simpa [S, (D.wall b).direction_support] using hv)
      exact Eventually.of_forall fun a => ⟨by
        simpa [sub_eq_add_neg, add_comm] using
          (S.vadd_mem_iff_mem_of_mem_direction (S.direction.smul_mem (-a) hv)).not.mpr hnot,
        by simpa [add_comm] using
          (S.vadd_mem_iff_mem_of_mem_direction (S.direction.smul_mem a hv)).not.mpr hnot⟩
    · have hneg : -v ∉ S.direction := fun hn => hv (by simpa using S.direction.neg_mem hn)
      filter_upwards [S.eventually_smul_vadd_notMem hv θ,
        S.eventually_smul_vadd_notMem hneg θ] with a ha hn
      exact ⟨by simpa [sub_eq_add_neg, add_comm] using hn,
        by simpa [add_comm] using ha⟩
  -- Realize the two regular crossings at the same sufficiently small offset.
  obtain ⟨a, ha⟩ := (hmiss.and
    ((D.eventually_exists_levelPathProduct_eq_combinedLabel k θ v hθ htrans).and
      (D.eventually_exists_levelPathProduct_eq_combinedLabel k (θ + w) v hη htrans'))).exists
  obtain ⟨x₀, x₁, e, hx₀, hx₁, he⟩ := ha.2.1
  obtain ⟨y₀, y₁, f, hy₀, hy₁, hf⟩ := ha.2.2
  -- The connecting sides stay in translates of the common tangent direction.
  have hside {x y : WallComplement (fun b : D.active k => (D.wall b).support)}
      (hxy : y.val = x.val + w)
      (hx : ∀ b : D.active k, x.val ∉ affineSpan ℝ (D.wall b).support) :
      crossings x y = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨b, t⟩ ht
    have hp := subset_affineSpan ℝ _ ((mem_crossings x y b t).mp ht).2
    have hd := (affineSpan ℝ (D.wall b).support).vadd_mem_iff_mem_of_mem_direction
      ((affineSpan ℝ (D.wall b).support).direction.smul_mem t (hwd b)) (p := x.val)
    apply hx b
    apply hd.mp
    have he : AffineMap.lineMap x.val y.val t = t • w +ᵥ x.val := by
      simp only [AffineMap.lineMap_apply_module, hxy, vadd_eq_add]
      module
    exact he ▸ hp
  have hc₀ : crossings x₀ y₀ = ∅ := hside (by rw [hx₀, hy₀]; module)
    (fun b => hx₀ ▸ (ha.1 b).1)
  have hc₁ : crossings x₁ y₁ = ∅ := hside (by rw [hx₁, hy₁]; module)
    (fun b => hx₁ ▸ (ha.1 b).2)
  let r₀ : x₀ ⟶ y₀ := ⟨.of_crossings_eq_empty
    (fun b => (D.wall b).isConvexPolyhedron.isClosed) hc₀⟩
  let r₁ : x₁ ⟶ y₁ := ⟨.of_crossings_eq_empty
    (fun b => (D.wall b).isConvexPolyhedron.isClosed) hc₁⟩
  have hprod {x y : WallComplement (fun b : D.active k => (D.wall b).support)}
      (r : x ⟶ y) (hr : crossings x y = ∅) : D.levelPathProduct k r.toPath = 1 := by
    rw [D.levelPathProduct_eq_wallPathProduct k r.toPath (D.activeLabels_commute k),
      Quiver.Path.wallPathProduct_toPath]
    exact segmentPathProduct_eq_one_of_crossings_eq_empty _ _ _ r hr
  -- The two routes have equal products; both connecting factors are identities.
  have hc := (D.levelConsistent_def k).mp hD
    (e.toPath.comp r₁.toPath) (r₀.toPath.comp f.toPath)
  simpa only [D.levelPathProduct_comp, he, hf, hprod r₀ hc₀, hprod r₁ hc₁,
    one_mul, mul_one] using hc.symm

end Mei.DirectedDiagram
