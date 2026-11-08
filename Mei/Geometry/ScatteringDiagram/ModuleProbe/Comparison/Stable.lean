/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Uniform

/-!
# Probe comparison at locally stable ray endpoints

The independently constructed probe field equals the actual weighted ray sum at
every allowed endpoint where that sum is locally constant. In particular this
holds off the frontiers of the complete decorated-type domains, without requiring
the endpoint to avoid the auxiliary arrangements used to compare recursions.
The actual ray sums consequently obey coefficient path transport between these
endpoints, including paths crossing ordinary walls.

The extension uses density of the common generic locus, local constancy of the
extended probe field, and the finite complete-type expansion of ray evaluation.
It retains the original full incoming histories and makes no admissibility claim
for limiting rays on type-domain frontiers. The comparison follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')
  (hinitial : ∀ c, D.wall (.inl c) =
    (initialDiagram d ℳ p ℒ H h h' D₀ a).wall c)
  (K : ℕ) (hBc : B.LevelConsistent K)
  (hD : D.LevelConsistent (K + 1))
  (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
    (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
    (cylinderDiagram d ℳ p ℒ H h h' B) K)
  (hout : ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ D.active (K + 1) →
    (p + n.val, 1) ∈ (D.wall (.inr c)).ray.rayDegrees →
      (D.wall (.inr c)).Outgoing)
  (b : (d.shiftedQuotientGrading ℳ p K).piece 0)

local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B K hBc
local notation "evaluation" => cutoffWallEventEvaluation d ℳ p ℒ H h B
  K K (Nat.le_refl _) b univ
local notation "types" => PathDecoratedType (Q := Quiver.SingleObj (WallEvent (B.active K)))
  (fun e => wallEventPropagation d ℳ p ℒ H h B K K (Nat.le_refl _) e)
  (fun _ => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p K)) 0 b
  (wallEventPaths d ℒ H h B K K)
  (fun _ n => i (ρ (p + n))) (fun e => WallEvent.normal e (B.activeNormal K)) (fun e => Prod.snd e)
local notation "domain" => fun t : types => admissibleBackwardDomain
  (Quiver.Path.reverseArrowLabels (fun e => WallEvent.normal e (B.activeNormal K))
    (Subtype.val (Sigma.fst t)))
  (Quiver.Path.reverseArrowLabels (fun e => WallEvent.offset e (B.activeOffset K))
    (Subtype.val (Sigma.fst t)))
  (Quiver.Path.Degrees.reverseVertexLabels (fun _ n => i (ρ (p + n))) 0
    (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
  (Quiver.Path.reverseArrowLabels (fun e => WallEvent.support e (B.activeSupport K))
    (Subtype.val (Sigma.fst t)))
  (B.activeSupport K) (fun _ : Unit => singularSupport (B.activeSupport K)) (univ : Set V)

include hinitial hBc hD hB hout

/-- Extend the independent probe/ray comparison to any allowed endpoint at
which the actual weighted evaluation is locally constant. The point may belong
to the auxiliary exceptional arrangements used in the recursion comparison. -/
theorem extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq
    (hb : d.shiftedQuotientComponent ℳ p p K (by simp only [sub_self, map_zero]; omega)
    b = a)
    (x : WallComplement (B.activeSupport K))
    (hx : ∀ᶠ Q in 𝓝 x.val, evaluation Q = evaluation x.val) :
    field x = evaluation x.val := by
  let := h.finiteDimensional
  obtain ⟨F, hF⟩ := exists_extendedCoefficientField_eq_cutoffWallEventEvaluation
    d ℳ p ℒ H h h' D₀ a D B hinitial K hBc hD hB hout b hb
  let U : Set V := {Q | ∀ c : B.active K, Q ∉ (B.wall c).support}
  have hU : IsOpen U := by
    simpa only [U, ofPred_forall, compl_def] using isOpen_iInter_of_finite
      (fun c : B.active K => (B.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  let z : U := ⟨x.val, x.notMem⟩
  have hd : Dense {y : U | ∀ n, (F n).IsGeneric y.val} :=
    (ExceptionalArrangement.dense_iInter_isGeneric F).preimage hU.isOpenMap_subtype_val
  have hprobe := (isLocallyConstant_extendedCoefficientField
    d ℳ p ℒ H h h' D B K hBc).eventually_eq z
  have hray := (continuous_subtype_val.tendsto z).eventually hx
  obtain ⟨W, hWeq, hW, hzW⟩ := mem_nhds_iff.mp (hprobe.and hray)
  obtain ⟨y, hy, hyW⟩ := hd.exists_mem_open hW ⟨z, hzW⟩
  obtain ⟨hallow, heq⟩ := hF y.val hy
  obtain ⟨hp, hr⟩ := hWeq hyW
  exact hp.symm.trans (heq.trans hr)

/-- Off the frontiers of the actual complete type domains, the finite probe
field is the weighted sum of actual rays. Only the base walls must be avoided;
no auxiliary probe or recursion genericity is imposed at the endpoint. -/
theorem extendedCoefficientField_eq_cutoffWallEventEvaluation_of_notMem_frontier
    (hb : d.shiftedQuotientComponent ℳ p p K (by simp only [sub_self, map_zero]; omega)
    b = a)
    (x : WallComplement (B.activeSupport K))
    (hx : ∀ t : types, x.val ∉ frontier (domain t)) :
    field x = evaluation x.val := by
  apply extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq
    d ℳ p ℒ H h h' D₀ a D B hinitial K hBc hD hB hout b hb x
  simp only [cutoffWallEventEvaluation_def]
  exact pathDecoratedEvaluation_eventually_eq_of_notMem_frontier _ _ _ _ _ _ _ _ _ _ _ _ _ x.val hx

/-- Actual weighted ray sums at endpoints off all complete type-domain frontiers
are related by the base path product along any admissible path. The incoming
source is still the whole space, even when the path visits only a small region. -/
theorem cutoffWallEventEvaluation_eq_truncatedBCHAction_levelPathProduct
    (hb : d.shiftedQuotientComponent ℳ p p K (by simp only [sub_self, map_zero]; omega)
    b = a)
    {x y : WallComplement (B.activeSupport K)} (γ : AdmissiblePLPath x y)
    (hx : ∀ t : types, x.val ∉ frontier (domain t))
    (hy : ∀ t : types, y.val ∉ frontier (domain t)) :
    evaluation y.val = (d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ K
      (B.levelPathProduct K γ) (evaluation x.val) := by
  rw [← extendedCoefficientField_eq_cutoffWallEventEvaluation_of_notMem_frontier
    d ℳ p ℒ H h h' D₀ a D B hinitial K hBc hD hB hout b hb y hy,
    ← extendedCoefficientField_eq_cutoffWallEventEvaluation_of_notMem_frontier
      d ℳ p ℒ H h h' D₀ a D B hinitial K hBc hD hB hout b hb x hx,
    extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B K hBc x y,
    B.levelTransport_eq_levelPathProduct hBc γ]

end Mei.ModuleProbe
