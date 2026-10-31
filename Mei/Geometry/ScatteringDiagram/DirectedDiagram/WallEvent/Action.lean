/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallEvent
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing.Action
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay

/-!
# Normal velocity under simultaneous wall events

The fixed label of a signed simultaneous event preserves normal degree on
filtered coefficient quotients. Every surviving whole-component history of
these labels therefore preserves normal velocity at every encounter. Relative
coefficient degrees are translated by the ambient shift before computing
velocity. Coincident indexed walls can have different supported rays and opposite
coorientations; no single-ray hypothesis on their combined label is imposed.

We use the normal-degree preservation of `DirectedDiagram.combinedLabel`,
its comparison with `DirectedDiagram.wallEventLabel`, and
`homogeneousHistory_rel_of_ne_zero`.
Whole-component propagation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.10 and §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L M V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ]

local notation "walls" k => fun j : D.active k => DirectedWall.support (DirectedDiagram.wall D j)
local notation "f" k => fun j : D.active k => h.continuousRealCharacter
  (DirectedWall.normal (DirectedDiagram.wall D j))

/-- The canonical fixed label preserves and reflects the normal-degree fibers
of its chosen incident normal, including unrealizable events with label one. -/
@[simp↓] -- Preserve membership before expanding the exponential action.
theorem truncatedBCHAction_wallEventLabel_mem_normalDegreeSubmodule_iff
    (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F] (k : ℕ)
    (e : WallEvent (D.active k)) (z : ℤ) (a : F.quotient k) :
    F.truncatedBCHAction d ℒ k (D.wallEventLabel k e) a ∈
        (normalDegreeSubmodule ρ ℳ (D.wall e.1.property.choose).normal z).map
          (F.submodule (k + 1)).mkQ ↔
      a ∈ (normalDegreeSubmodule ρ ℳ (D.wall e.1.property.choose).normal z).map
        (F.submodule (k + 1)).mkQ := by
  classical
  by_cases hex : ∃ x v, x ∈ e.support (walls k) ∧ x ∉ singularSupport (walls k) ∧
      SignType.sign (e.normal (f k) v) = e.2 ∧ e.normal (f k) v ≠ 0
  · obtain ⟨x, v, hx, hreg, hs, hv⟩ := hex
    rw [D.wallEventLabel_eq_combinedLabel k e hx hreg hs hv]
    exact D.truncatedBCHAction_combinedLabel_mem_normalDegreeSubmodule_iff ℳ F k x (-v)
      hreg e.1.property.choose (e.support_subset (walls k) e.1.property.choose_spec hx) z a
  · rw [D.wallEventLabel_eq_one_of_not_exists k e hex, map_one,
      LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]

/-- Every surviving component of a fixed event action has the normal degree
of its homogeneous input. The coefficient grading is any inherited quotient
grading, and the input can be an arbitrary homogeneous quotient class. -/
theorem normal_eq_of_decompose_truncatedBCHAction_wallEventLabel_ne_zero
    (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F] (k : ℕ)
    (𝓝 : Γ → Submodule R (F.quotient k)) [DirectSum.Decomposition 𝓝]
    (h𝓝 : ∀ n, 𝓝 n = (ℳ n).map (F.submodule (k + 1)).mkQ)
    (e : WallEvent (D.active k)) {p q : Γ} {a : F.quotient k}
    (ha : a ∈ 𝓝 p)
    (hq : DirectSum.decompose 𝓝 (F.truncatedBCHAction d ℒ k (D.wallEventLabel k e) a) q ≠ 0) :
    (D.wall e.1.property.choose).normal (ρ q) =
      (D.wall e.1.property.choose).normal (ρ p) := by
  let m := (D.wall e.1.property.choose).normal
  have hN : normalDegreeSubmodule ρ 𝓝 m (m (ρ p)) =
      (normalDegreeSubmodule ρ ℳ m (m (ρ p))).map (F.submodule (k + 1)).mkQ := by
    rw [map_normalDegreeSubmodule]
    congr 1
    exact funext h𝓝
  have haN := le_normalDegreeSubmodule (ρ := ρ) 𝓝 m p ha
  rw [hN] at haN
  have hb := (D.truncatedBCHAction_wallEventLabel_mem_normalDegreeSubmodule_iff
    ℳ F k e (m (ρ p)) a).mpr haN
  rw [← hN, mem_normalDegreeSubmodule_iff] at hb
  by_contra hne
  exact hq (Subtype.ext (hb q hne))

end Mei.DirectedDiagram

namespace Mei.DirectedDiagram

variable {Γ : Type} {Λ R L M V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ]

local notation "walls" k => fun j : D.active k => DirectedWall.support (DirectedDiagram.wall D j)
local notation "f" k => fun j : D.active k => h.continuousRealCharacter
  (DirectedWall.normal (DirectedDiagram.wall D j))

variable [DirectSum.Decomposition ℳ] (p : Γ) (k : ℕ)

local notation "G" => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "T" => fun e : WallEvent (D.active k) => LinearEquiv.toLinearMap
  (ModuleFiltration.truncatedBCHAction (d.shiftedLieFiltration ℒ ℳ p) d ℒ k
    (DirectedDiagram.wallEventLabel D k e))
local notation "v" => fun r : Γ => i (ρ (p + r))

/-- Surviving histories of canonical simultaneous events preserve real normal
velocity at every step. Velocities use ambient degrees; the coefficient grading
uses relative degrees. Inverse labels and shifts with zero spatial projection
are included. -/
theorem homogeneousHistory_wallEventLabel_normal_eq {n : ℕ}
    (e : Fin n → WallEvent (D.active k)) (r : Fin n → Γ) (r₀ : Γ)
    (a : G r₀) (hne : homogeneousHistory G (fun j => T (e j)) r a ≠ 0) (j : Fin n) :
    (e j).normal (f k) (v (r j)) =
      (e j).normal (f k) (v (Fin.snoc (α := fun _ => Γ) r r₀ j.succ)) := by
  have := d.shiftedGrading_gradedBracket ℒ ℳ p
  have he := homogeneousHistory_rel_of_ne_zero G (fun j => T (e j))
    (fun j _ _ _ ha hq =>
      D.normal_eq_of_decompose_truncatedBCHAction_wallEventLabel_ne_zero
        (M := d.shiftedLieSubmodule ℒ ℳ p) (shiftedGrading ℳ d.monoid p)
        (d.shiftedLieFiltration ℒ ℳ p) k G
        (d.shiftedQuotientGrading_piece ℳ p k) (e j) ha hq)
    r r₀ a hne j
  have hamb : (D.wall (e j).1.property.choose).normal (ρ (p + r j)) =
      (D.wall (e j).1.property.choose).normal
        (ρ (p + Fin.snoc (α := fun _ => Γ) r r₀ j.succ)) := by
    simp only [map_add, he]
  simpa only [WallEvent.normal_def, h.continuousRealCharacter_apply, h.realCharacter_apply]
    using congrArg (Int.cast : ℤ → ℝ) hamb

/-- For actual signed simultaneous event labels, the decorated-history filter
requires only survival and the prescribed crossing signs: normal conservation
is automatic, even when several supported rays contribute to the event. -/
@[simp↓]
theorem mem_decoratedHistorySupport_wallEventLabel_iff {n : ℕ}
    (e : Fin n → WallEvent (D.active k)) (r : Fin n → Γ) (r₀ : Γ)
    (a : G r₀) :
    r ∈ decoratedHistorySupport G (fun j => T (e j)) r₀ a v
      (fun j => (e j).normal (f k)) (fun j => (e j).2) ↔
      homogeneousHistory G (fun j => T (e j)) r a ≠ 0 ∧
        ∀ j, SignType.sign ((e j).normal (f k) (v (r j))) = (e j).2 := by
  rw [mem_decoratedHistorySupport]
  constructor
  · exact fun hr => ⟨hr.1, fun j => (hr.2 j).2⟩
  · rintro ⟨hne, hs⟩
    exact ⟨hne, fun j =>
      ⟨D.homogeneousHistory_wallEventLabel_normal_eq ℳ p k e r r₀ a hne j, hs j⟩⟩

end Mei.DirectedDiagram
