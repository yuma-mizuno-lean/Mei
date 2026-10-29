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
-/

public noncomputable section

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

end Mei.DirectedDiagram
