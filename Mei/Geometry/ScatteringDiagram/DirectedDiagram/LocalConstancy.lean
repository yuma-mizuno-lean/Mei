/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing

/-!
# Local constancy along regular wall germs

Near a regular point, moving tangentially to every incident wall preserves the
incident indexed walls and their combined crossing label. The crossing vector
is fixed, and no consistency hypothesis is needed. Repeated or overlapping
supports retain their indexed multiplicities.

The geometric input is `Mei.Convex.eventually_mem_iff_of_submodule_le_direction`.
The combined-label API then lets coefficient constructions use this local
constancy without choosing an enumeration of the incident walls.

In particular, near a regular point of an affine subspace `A` all of whose incident walls span
`A`, the nearby points of `A` lie on the same walls and have the same combined label
(`DirectedDiagram.eventually_nhdsWithin_combinedLabel_eq`).
-/

open TauCeti (singularSupport isClosed_singularSupport)

public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Sufficiently small displacements tangent to all incident active walls preserve
their combined label, for every fixed crossing vector. Regularity of the displaced
point follows on the same neighbourhood. -/
theorem eventually_combinedLabel_add_eq (k : ℕ) (θ : V)
    (hθ : θ ∉ singularSupport (fun a : D.active k => (D.wall a).support))
    (S : Submodule ℝ V)
    (hS : ∀ a : D.active k, θ ∈ (D.wall a).support →
      S ≤ (affineSpan ℝ (D.wall a).support).direction) :
    ∀ᶠ w : S in 𝓝 0,
      ∃ hη : θ + (w : V) ∉ singularSupport (fun a : D.active k => (D.wall a).support),
        ∀ v, D.combinedLabel k (θ + (w : V)) v hη = D.combinedLabel k θ v hθ := by
  let := h.finiteDimensional
  have ht : Tendsto (fun w : S => θ + (w : V)) (𝓝 0) (𝓝 θ) := by
    have hc : Continuous (fun w : S => θ + (w : V)) := by fun_prop
    simpa using hc.tendsto (0 : S)
  have hreg := ht.eventually ((isClosed_singularSupport
    (fun a : D.active k => (D.wall a).support)
    (fun a => (D.wall a).isConvexPolyhedron.isClosed)).isOpen_compl.mem_nhds hθ)
  filter_upwards [hreg, eventually_mem_iff_of_submodule_le_direction
    (fun a : D.active k => (D.wall a).support)
    (fun a => (D.wall a).isConvexPolyhedron.isClosed) θ hθ S hS] with w hw hmem
  refine ⟨hw, fun v => ?_⟩
  classical
  let I := (Set.toFinite {a : D.active k | θ ∈ (D.wall a).support}).toFinset
  have hI (a : D.active k) : a ∈ I.toList ↔ θ ∈ (D.wall a).support := by simp [I]
  rw [D.combinedLabel_eq_prod k (θ + (w : V)) v hw I.toList I.nodup_toList
    (fun a => (hI a).trans (hmem a).symm),
    D.combinedLabel_eq_prod k θ v hθ I.toList I.nodup_toList hI]

/-- **Local constancy along an affine subspace.** Let `θ` be a point of the affine subspace `A`,
outside the singular support of the walls active at order `k`, such that every active wall
through `θ` has affine span `A`. Then the points of `A` near `θ` are outside that singular
support, lie on exactly the same active walls as `θ`, and have the same combined label as `θ`
in every direction. -/
theorem eventually_nhdsWithin_combinedLabel_eq (k : ℕ) {A : AffineSubspace ℝ V} {θ : V}
    (hθA : θ ∈ A) (hθ : θ ∉ singularSupport (fun a : D.active k => (D.wall a).support))
    (hA : ∀ a : D.active k, θ ∈ (D.wall a).support → affineSpan ℝ (D.wall a).support = A) :
    ∀ᶠ η in 𝓝[(A : Set V)] θ,
      ∃ hη : η ∉ singularSupport (fun a : D.active k => (D.wall a).support),
        (∀ a : D.active k, η ∈ (D.wall a).support ↔ θ ∈ (D.wall a).support) ∧
          ∀ v, D.combinedLabel k η v hη = D.combinedLabel k θ v hθ := by
  let := h.finiteDimensional
  have hS (a : D.active k) (ha : θ ∈ (D.wall a).support) :
      A.direction ≤ (affineSpan ℝ (D.wall a).support).direction := by
    rw [hA a ha]
  have hev := (D.eventually_combinedLabel_add_eq k θ hθ A.direction hS).and
    (eventually_mem_iff_of_submodule_le_direction _
      (fun a : D.active k => (D.wall a).isConvexPolyhedron.isClosed) θ hθ A.direction hS)
  -- Move from displacements in the direction of `A` near `0` to points of `A` near `θ`.
  rw [nhds_subtype, Submodule.coe_zero, eventually_comap] at hev
  have hc : Tendsto (fun η => η - θ) (𝓝[(A : Set V)] θ) (𝓝 0) := by
    simpa using ((continuous_sub_right θ).tendsto θ).mono_left nhdsWithin_le_nhds
  filter_upwards [hc.eventually hev, self_mem_nhdsWithin] with η hη hηA
  obtain ⟨⟨hη', hl⟩, hm⟩ := hη ⟨η - θ, AffineSubspace.vsub_mem_direction hηA hθA⟩ rfl
  simp only [add_sub_cancel] at hη' hl hm
  exact ⟨hη', hm, hl⟩

end Mei.DirectedDiagram
