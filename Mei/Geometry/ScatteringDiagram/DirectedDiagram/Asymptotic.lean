/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Escape

/-!
# Degreewise asymptotics of regular wall germs

Translate a compact set in the positive spatial direction of a fixed degree.
Eventually the component of that degree in every regular combined wall logarithm
is the signed contribution of the incoming full hyperplanes at the original
point. Only incoming walls whose supported rays contain the selected degree
need be full hyperplanes. Outgoing walls on those rays escape uniformly; all
other walls have zero component in that degree. In particular an outgoing
family has eventually zero component, even if other degrees remain visible.

These are exact eventual equalities, uniform in the crossing vector and compact
set, with no consistency or pure-birth-logarithm assumption. They supply the
asymptotic initial values used in coefficient recursions for module probes.
Regularity at the translated point is a hypothesis of each germ evaluation;
the translation is not asserted to avoid singular support.

The proof combines `DirectedDiagram.log_combinedLabel_eq_sum`,
`DirectedWallSpaces.decompose_log_projection_eq_zero_of_notMem_rayDegrees`, and
`DirectedWall.Outgoing.eventually_forall_notMem_support_of_mem_rayDegrees`.
The geometric argument follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

open scoped Classical in
/-- Far along a degree direction, the component of a regular germ logarithm is
the signed sum of its incoming hyperplane contributions at the original point.
The bound is uniform on a compact set and in the crossing vector. Only incoming
walls on rays carrying this degree must be full hyperplanes. -/
theorem eventually_decompose_log_combinedLabel_eq_sum_incoming (k : ℕ) (n : Γ)
    (hfull : ∀ a : D.active k, (D.wall a).Incoming → n ∈ (D.wall a).ray.rayDegrees →
      ∃ c : ℝ, (D.wall a).support = {x | h.realCharacter (D.wall a).normal x = c})
    {K : Set V} (hK : IsCompact K) :
    let _ := Fintype.ofFinite (D.active k)
    ∀ᶠ t : ℝ in atTop, ∀ θ ∈ K, ∀ v : V,
      ∀ hθ : θ + t • i (ρ n) ∉
        singularSupport (fun a : D.active k => (D.wall a).support),
      DirectSum.decompose (d.truncatedGrading ℒ k)
          (BCHGroup.log (D.combinedLabel k (θ + t • i (ρ n)) v hθ)) n =
        ∑ a : D.active k,
          if (D.wall a).Incoming ∧ θ ∈ (D.wall a).support then
            (if 0 < h.realCharacter (D.wall a).normal v then -1 else 1 : ℤ) •
              DirectSum.decompose (d.truncatedGrading ℒ k)
                (BCHGroup.log (L := d.truncatedLie ℒ k)
                  (CompletedGroup.projection k (D.wall a).label)) n else 0 := by
  classical
  let := Fintype.ofFinite (D.active k)
  -- Only outgoing walls carrying this degree need to escape. The finite
  -- intersection gives one bound for all of them and for the whole compact set.
  have hescape : ∀ᶠ t : ℝ in atTop, ∀ a : D.active k,
      (D.wall a).Outgoing → n ∈ (D.wall a).ray.rayDegrees →
        ∀ θ ∈ K, θ + t • i (ρ n) ∉ (D.wall a).support := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases hout : (D.wall a).Outgoing
    · by_cases hn : n ∈ (D.wall a).ray.rayDegrees
      · exact (hout.eventually_forall_notMem_support_of_mem_rayDegrees hn hK).mono
          fun _ ht _ _ => ht
      · exact Filter.Eventually.of_forall fun _ _ hn' => (hn hn').elim
    · exact Filter.Eventually.of_forall fun _ hout' => (hout hout').elim
  filter_upwards [hescape] with t ht θ hθK v hθ
  let pr : d.truncatedLie ℒ k →ₗ[R] d.truncatedGrading ℒ k n :=
    (DirectSum.component R Γ (fun m => d.truncatedGrading ℒ k m) n).comp
      (DirectSum.decomposeLinearEquiv (d.truncatedGrading ℒ k)).toLinearMap
  -- This is the standard linear component projection, so maps of sums and
  -- integer multiples apply to the homogeneous decomposition.
  have hpr (x : d.truncatedLie ℒ k) :
      pr x = DirectSum.decompose (d.truncatedGrading ℒ k) x n := (rfl)
  have hlog := congrArg pr (D.log_combinedLabel_eq_sum k (θ + t • i (ρ n)) v hθ)
  simp only [map_sum, apply_ite, map_zsmul, map_zero] at hlog
  simp only [hpr] at hlog
  rw [hlog]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hn : n ∈ (D.wall a).ray.rayDegrees
  · by_cases hin : (D.wall a).Incoming
    · obtain ⟨c, hc⟩ := hfull a hin hn
      have hnormal : h.realCharacter (D.wall a).normal (i (ρ n)) = 0 := by
        obtain ⟨-, b, -, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
        simp [h.realCharacter_apply, (D.wall a).normal_direction]
      have hmem : θ + t • i (ρ n) ∈ (D.wall a).support ↔ θ ∈ (D.wall a).support := by
        rw [hc]
        simp only [mem_ofPred_eq, map_add, map_smul, hnormal, smul_zero, add_zero]
      simp only [hmem, hin, true_and]
    · have hout : (D.wall a).Outgoing := by
        simpa only [(D.wall a).outgoing_iff, (D.wall a).incoming_iff, mem_recessionCone] using hin
      simp only [ht a hout hn θ hθK, hin, false_and, ite_false]
  · have hz : DirectSum.decompose (d.truncatedGrading ℒ k)
        (BCHGroup.log (L := d.truncatedLie ℒ k)
          (CompletedGroup.projection k (D.wall a).label)) n = 0 := by
      apply Subtype.ext
      exact H.decompose_log_projection_eq_zero_of_notMem_rayDegrees (D.wall a).label_mem k hn
    simp only [hz, smul_zero, ite_self]

/-- If the active walls carrying degree `n` are outgoing, far-translated regular
germ logarithms have zero component in that degree. Walls on other rays are
unrestricted. -/
theorem eventually_decompose_log_combinedLabel_eq_zero_of_outgoing (k : ℕ) (n : Γ)
    (hout : ∀ a : D.active k, n ∈ (D.wall a).ray.rayDegrees → (D.wall a).Outgoing)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ θ ∈ K, ∀ v : V,
      ∀ hθ : θ + t • i (ρ n) ∉
        singularSupport (fun a : D.active k => (D.wall a).support),
      DirectSum.decompose (d.truncatedGrading ℒ k)
        (BCHGroup.log (D.combinedLabel k (θ + t • i (ρ n)) v hθ)) n = 0 := by
  classical
  filter_upwards [D.eventually_decompose_log_combinedLabel_eq_sum_incoming k n
    (fun a hin hn => by
      have hnot : ¬ (D.wall a).Incoming := by
        simpa only [(D.wall a).outgoing_iff, (D.wall a).incoming_iff,
          mem_recessionCone] using hout a hn
      exact (hnot hin).elim)
    hK] with t ht θ hθK v hθ
  rw [ht θ hθK v hθ]
  apply Finset.sum_eq_zero
  intro a _
  by_cases hn : n ∈ (D.wall a).ray.rayDegrees
  · have hin : ¬ (D.wall a).Incoming :=
      by simpa only [(D.wall a).outgoing_iff, (D.wall a).incoming_iff,
          mem_recessionCone] using hout a hn
    simp only [hin, false_and, ite_false]
  · have hz : DirectSum.decompose (d.truncatedGrading ℒ k)
        (BCHGroup.log (L := d.truncatedLie ℒ k)
          (CompletedGroup.projection k (D.wall a).label)) n = 0 := by
      apply Subtype.ext
      exact H.decompose_log_projection_eq_zero_of_notMem_rayDegrees (D.wall a).label_mem k hn
    simp only [hz, smul_zero, ite_self]

end Mei.DirectedDiagram
