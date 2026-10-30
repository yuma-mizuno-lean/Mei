/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Component
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Field
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Asymptotic

/-!
# Asymptotic initial values of probe coefficients

In an extension of a cylinder input and its probe wall, translate in
the positive spatial direction of a charge-one degree. Eventually the component
of that degree in every regular vertical coefficient is the component of the
original incoming coefficient. The bound is uniform over a compact subset of
the probe hyperplane. Only additional active walls carrying this degree must
be outgoing. Other homogeneous components need not stabilize there.

This specializes `DirectedDiagram.eventually_decompose_log_combinedLabel_eq_sum_incoming`:
base cylinders have no charge-one component, outgoing walls escape, and the
initial probe contributes with the negative upward-crossing sign. The germ
statement needs neither consistency nor pure birth logarithms nor a nonzero
projected spatial direction.
For a consistent diagram, regular heights in a bounded moving interval
remove the germ-regularity hypothesis and give initial values of the actual
endpoint field. Components with zero spatial direction consequently have their
initial value at every generic endpoint, without a nonzero-velocity assumption.

The asymptotic initial condition is the one used by Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5), in the coefficient recursion for theta functions.
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))

local notation "v" => (0, j (0, 1))
local notation "G" => PositiveDegrees.truncatedLie (positiveDegrees d p) (grading d ℳ p ℒ)
local notation "ℋ" => PositiveDegrees.truncatedGrading (positiveDegrees d p) (grading d ℳ p ℒ)

open scoped Classical in
private theorem sum_incoming_coefficient
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (q : Γ) (hk : d.degree (q - p) ≤ k)
    (hout : ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    (θ : V × E) (hplane : (h.prod h').realCharacter probeNormal θ = 0) :
    let _ := Fintype.ofFinite (D.active (k + 1))
    let P := (d.shiftedQuotientComponent ℳ p q k hk).comp
      (moduleQuotientProjection d ℳ p ℒ k)
    ∑ b : D.active (k + 1),
      (if (D.wall b).Incoming ∧ θ ∈ (D.wall b).support then
        (if 0 < (h.prod h').realCharacter (D.wall b).normal v then -1 else 1 : ℤ) •
          P (BCHGroup.log (CompletedGroup.projection (k + 1) (D.wall b).label)) else 0) =
      -DirectSum.decompose ℳ (a : M) q := by
  classical
  let := Fintype.ofFinite (D.active (k + 1))
  dsimp only
  let P : G (k + 1) →ₗ[R] ℳ q :=
    (d.shiftedQuotientComponent ℳ p q k hk).comp
      (moduleQuotientProjection d ℳ p ℒ k)
  have hP (x : G (k + 1)) :
      P (DirectSum.decompose (ℋ (k + 1)) x (q, 1, 0)) = P x :=
    shiftedQuotientComponent_moduleQuotientProjection_decompose d ℳ p ℒ q k hk x
  have hnot (b : κ) (hb : Sum.inr b ∈ D.active (k + 1))
      (hn : (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees) :
      ¬ (D.wall (.inr b)).Incoming := by
    simpa only [DirectedWall.outgoing_iff, DirectedWall.incoming_iff, mem_recessionCone]
      using hout b hb hn
  -- Base cylinders have zero charge-one component, while the probe recovers the input.
  have hbase (b : ι) :
      P (BCHGroup.log (CompletedGroup.projection (k + 1)
        (D.wall (.inl (.inl b))).label)) = 0 := by
    rw [← hP]
    have hz := (wallSpaces d ℳ p ℒ H).decompose_log_projection_eq_zero_of_notMem_rayDegrees
      (D.wall (.inl (.inl b))).label_mem (k + 1) (n := (q, 1, 0)) (by
        simp only [hinitial, initialDiagram_wall_inl, baseCylinder_ray,
          mem_baseRay_rayDegrees, one_ne_zero, false_and, and_false, not_false_eq_true])
    rw [hz, map_zero]
  have hprobe :
      P (BCHGroup.log (CompletedGroup.projection (k + 1)
        (D.wall (.inl (.inr ()))).label)) = DirectSum.decompose ℳ (a : M) q := by
    simp only [hinitial, initialDiagram_wall_inr, probeWall_label,
      PositiveDegrees.projection_expToCompletion, BCHGroup.log_exp,
      LieIdeal.mkQ_apply, P, LinearMap.comp_apply, moduleQuotientProjection_mk,
      LinearEquiv.apply_symm_apply, PositiveDegrees.shiftedQuotientComponent_mk,
      moduleInclusion, LieAlgebra.SemiDirectSum.inl_eq_mk]
  have hterm (b : D.active (k + 1)) (hb : b.val ≠ .inl (.inr ())) :
      (if (D.wall b).Incoming ∧ θ ∈ (D.wall b).support then
        (if 0 < (h.prod h').realCharacter (D.wall b).normal v then -1 else 1 : ℤ) •
          P (BCHGroup.log (CompletedGroup.projection (k + 1) (D.wall b).label)) else 0) = 0 := by
    rcases b with ⟨((b | b) | b), hb'⟩
    · simp only [hbase, smul_zero, ite_self]
    · exact (hb (by cases b; rfl)).elim
    · by_cases hn : (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees
      · simp only [hnot b hb' hn, false_and, ite_false]
      · have hz := (wallSpaces d ℳ p ℒ H).decompose_log_projection_eq_zero_of_notMem_rayDegrees
          (D.wall (.inr b)).label_mem (k + 1) hn
        rw [← hP, hz, map_zero]
        simp only [smul_zero, ite_self]
  -- A zero input has no active probe; otherwise it is the unique surviving summand.
  by_cases ha : a = 0
  · subst a
    simp only [ZeroMemClass.coe_zero, DirectSum.decompose_zero, DirectSum.zero_apply,
      neg_zero]
    apply Finset.sum_eq_zero
    intro b _
    apply hterm b
    intro hb
    have hb' := b.property
    rw [hb, D.mem_active] at hb'
    rw [hinitial, initialDiagram_wall_inr] at hb'
    exact hb' ((projection_probeWall_label_eq_one_iff d ℳ p ℒ H h h' 0 (k + 1)).mpr
      (Or.inl rfl))
  · have hactive : Sum.inl (Sum.inr ()) ∈ D.active (k + 1) := by
      rw [D.mem_active, hinitial, initialDiagram_wall_inr]
      exact (projection_probeWall_label_eq_one_iff d ℳ p ℒ H h h' a (k + 1)).not.mpr
        (by simp [ha])
    let b₀ : D.active (k + 1) := ⟨.inl (.inr ()), hactive⟩
    rw [Finset.sum_eq_single b₀ (fun b _ hb => hterm b (by
      intro heq
      exact hb (Subtype.ext heq))) (by simp)]
    simp only [b₀]
    rw [hprobe]
    simp [hinitial, hplane]

/-- Far along a charge-one degree direction, each retained homogeneous component
of the vertical coefficient equals the corresponding component of the incoming
coefficient. The bound is uniform over compact sets in the probe hyperplane.
Only additional active walls carrying this degree must be outgoing; the base
input and additional walls on other rays are arbitrary. -/
theorem eventually_shiftedQuotientComponent_verticalCoefficient_eq
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (q : Γ) (hk : d.degree (q - p) ≤ k)
    (hout : ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    {K : Set (V × E)} (hK : IsCompact K)
    (hplane : ∀ θ ∈ K, (h.prod h').realCharacter probeNormal θ = 0) :
    ∀ᶠ t : ℝ in atTop, ∀ θ ∈ K,
      ∀ hθ : θ + t • (i (ρ q), j (1, 0)) ∉
        singularSupport (fun b : D.active (k + 1) => (D.wall b).support),
      d.shiftedQuotientComponent ℳ p q k hk
        (verticalCoefficient d ℳ p ℒ H h h' D k
          (θ + t • (i (ρ q), j (1, 0))) hθ) =
        DirectSum.decompose ℳ (a : M) q := by
  classical
  let := Fintype.ofFinite (D.active (k + 1))
  let P : G (k + 1) →ₗ[R] ℳ q :=
    (d.shiftedQuotientComponent ℳ p q k hk).comp
      (moduleQuotientProjection d ℳ p ℒ k)
  have hP (x : G (k + 1)) :
      P (DirectSum.decompose (ℋ (k + 1)) x (q, 1, 0)) = P x :=
    shiftedQuotientComponent_moduleQuotientProjection_decompose d ℳ p ℒ q k hk x
  have hnot (b : κ) (hb : Sum.inr b ∈ D.active (k + 1))
      (hn : (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees) :
      ¬ (D.wall (.inr b)).Incoming := by
    simpa only [DirectedWall.outgoing_iff, DirectedWall.incoming_iff, mem_recessionCone]
      using hout b hb hn
  -- Only the initial probe can be incoming on a charge-one ray.
  have hfull : ∀ b : D.active (k + 1), (D.wall b).Incoming →
      (q, 1, 0) ∈ (D.wall b).ray.rayDegrees →
      ∃ c : ℝ, (D.wall b).support =
        {x | (h.prod h').realCharacter (D.wall b).normal x = c} := by
    rintro ⟨((b | b) | b), hb⟩ hin hn
    · simp only [hinitial, initialDiagram_wall_inl, baseCylinder_ray,
        mem_baseRay_rayDegrees, one_ne_zero, false_and, and_false] at hn
    · refine ⟨0, ?_⟩
      simp only [hinitial, initialDiagram_wall_inr, probeWall_support, probeWall_normal]
      ext x
      simp
    · exact (hnot b hb hn hin).elim
  have he := D.eventually_decompose_log_combinedLabel_eq_sum_incoming
    (k + 1) (q, 1, 0) hfull hK
  -- Convert the spatial image of the extended degree to its product coordinates.
  simp only [spatialMap_apply, AddMonoidHom.coe_prodMap, Prod.map_apply] at he
  filter_upwards [he] with t ht θ hθK hθ
  have hsum := congrArg (fun x : ℋ (k + 1) (q, 1, 0) => P x)
    (ht θ hθK v hθ)
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_zero,
    apply_ite, map_zero, map_sum, map_zsmul, hP] at hsum
  have hvalue := hsum.trans
    (sum_incoming_coefficient d ℳ p ℒ H h h' D₀ a D hinitial k q hk hout θ (hplane θ hθK))
  rw [verticalCoefficient_def, map_neg]
  exact congrArg Neg.neg hvalue |>.trans (neg_neg _)

/-- Uniformly over compact sets of base endpoints, a retained component of the
endpoint field eventually equals the incoming component along its positive
spatial direction. The translated endpoint need only be generic: no regular
height is prescribed or assumed. Only active additional walls carrying the
selected degree must be outgoing. -/
theorem eventually_shiftedQuotientComponent_coefficientField_eq
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hD : D.LevelConsistent (k + 1))
    (q : Γ) (hk : d.degree (q - p) ≤ k)
    (hout : ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ Q ∈ K,
      ∀ hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric
          (Q + t • i (ρ q)),
      d.shiftedQuotientComponent ℳ p q k hk
        (coefficientField d ℳ p ℒ H h h' D k (Q + t • i (ρ q)) hQ) =
        DirectSum.decompose ℳ (a : M) q := by
  -- A compact interval of initial heights lets us choose a regular height after
  -- translation. A single prescribed moving height could remain singular forever.
  let K' : Set (V × E) :=
    (fun x : V × ℝ => (x.1, x.2 • j (1, 0))) '' (K ×ˢ Icc 0 1)
  have hK' : IsCompact K' := (hK.prod isCompact_Icc).image (by fun_prop)
  have hplane : ∀ θ ∈ K', (h.prod h').realCharacter probeNormal θ = 0 := by
    rintro _ ⟨⟨Q, s⟩, _, rfl⟩
    have hn : (probeNormal : (Λ × ℤ × ℤ) →+ ℤ) =
        (AddMonoidHom.snd ℤ ℤ).comp (AddMonoidHom.snd Λ (ℤ × ℤ)) := by
      ext ⟨x, c, l⟩
      simp
    rw [hn, (h.prod h').realCharacter_comp h'
      (AddMonoidHom.snd Λ (ℤ × ℤ)) (LinearMap.snd ℝ V E) (fun _ => rfl)]
    simp
  filter_upwards [eventually_shiftedQuotientComponent_verticalCoefficient_eq
    d ℳ p ℒ H h h' D₀ a D hinitial k q hk hout hK' hplane] with t ht Q hQK hQ
  obtain ⟨y, hy, hreg⟩ := exists_regular_height d ℳ p ℒ H h h' D k
    (Q + t • i (ρ q)) hQ isOpen_Ioo (nonempty_Ioo.mpr (lt_add_one t))
  have hmem : (Q, (y - t) • j (1, 0)) ∈ K' := by
    exact ⟨(Q, y - t), ⟨hQK, by constructor <;> linarith [hy.1, hy.2]⟩, rfl⟩
  have he : (Q, (y - t) • j (1, 0)) + t • (i (ρ q), j (1, 0)) =
      (Q + t • i (ρ q), y • j (1, 0)) := by
    simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, sub_add_cancel]
  have hvalue := ht (Q, (y - t) • j (1, 0)) hmem
    (by simpa only [he] using hreg)
  simp only [he] at hvalue
  rw [coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D k hD
    (Q + t • i (ρ q)) hQ y hreg]
  exact hvalue

/-- A retained component whose spatial direction is zero has its incoming value
at every generic endpoint. Height independence converts escape in the auxiliary
height direction into an exact identity at the unchanged base endpoint. -/
theorem shiftedQuotientComponent_coefficientField_eq_of_spatial_eq_zero
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hD : D.LevelConsistent (k + 1))
    (q : Γ) (hk : d.degree (q - p) ≤ k) (hq : i (ρ q) = 0)
    (hout : ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) :
    d.shiftedQuotientComponent ℳ p q k hk
        (coefficientField d ℳ p ℒ H h h' D k Q hQ) =
      DirectSum.decompose ℳ (a : M) q := by
  obtain ⟨t, ht⟩ := (eventually_shiftedQuotientComponent_coefficientField_eq
    d ℳ p ℒ H h h' D₀ a D hinitial k hD q hk hout (isCompact_singleton (x := Q))).exists
  simpa only [hq, smul_zero, add_zero] using ht Q (mem_singleton Q) (by
    simpa only [hq, smul_zero, add_zero] using hQ)

end Mei.ModuleProbe
