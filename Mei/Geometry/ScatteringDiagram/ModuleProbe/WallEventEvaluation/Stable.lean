/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation
public import Mei.Geometry.Convex.Polyhedron.Rational.SingularSupport
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Uniform

/-!
# Intrinsic stable loci of actual wall-event evaluations

Finite stability means allowedness and local constancy of the actual total ray
sum. It is independent of probe comparison and may include cancellation-stable
type-domain frontier points. The finite locus is open and maximal among allowed
open sets with locally constant evaluation. Rational complete-type domains make
it dense for every diagram and input; Baire gives the dense Gδ all-order locus.
No consistency or probe-completion assumptions are required.

We use exact finite rational-normal presentations of singular support, rational
complete-type domains, and the existing membership-arrangement and evaluation
stability theorems. The complete endpoint constraints follow the geometric
interpretation in Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg
models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H κ')

/-- Allowed endpoints where the actual weighted ray sum is locally constant.
This locus is intrinsic to the total evaluation, so cancellations can include
points on individual type-domain frontiers. -/
def stableWallEventLocus (K : ℕ) (b : (d.shiftedQuotientGrading ℳ p K).piece 0) : Set V :=
  {Q | (∀ c : B.active K, Q ∉ (B.wall c).support) ∧
    ∀ᶠ Q' in 𝓝 Q,
      cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q' =
        cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q}

/-- Membership in the finite intrinsic stable locus is exactly allowedness
and local constancy of the actual total weighted evaluation. -/
@[simp]
theorem mem_stableWallEventLocus (K : ℕ)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0) (Q : V) :
    Q ∈ stableWallEventLocus d ℳ p ℒ H h B K b ↔
      (∀ c : B.active K, Q ∉ (B.wall c).support) ∧
      ∀ᶠ Q' in 𝓝 Q,
        cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q' =
          cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q := Iff.rfl

/-- The finite intrinsic stable locus is open, with no consistency or probe
hypotheses needed. -/
theorem isOpen_stableWallEventLocus (K : ℕ)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0) :
    IsOpen (stableWallEventLocus d ℳ p ℒ H h B K b) := by
  have hU : IsOpen {Q | ∀ c : B.active K, Q ∉ (B.wall c).support} := by
    simpa only [ofPred_forall, compl_def] using isOpen_iInter_of_finite
      (fun c : B.active K => (B.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  apply isOpen_iff_eventually.mpr
  intro Q hQ
  rw [mem_stableWallEventLocus] at hQ
  filter_upwards [hU.mem_nhds hQ.1, hQ.2, eventually_eventually_nhds.mpr hQ.2]
    with Q' hallow heq hnear
  exact (mem_stableWallEventLocus d ℳ p ℒ H h B K b Q').mpr
    ⟨hallow, hnear.mono fun Q'' h => h.trans heq.symm⟩


/-- Among open sets of allowed endpoints, the intrinsic stable locus is maximal
for local constancy of the actual evaluation. This criterion includes stable
total sums even when individual decorated types change. -/
theorem subset_stableWallEventLocus_iff (K : ℕ)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0) (U : Set V) (hU : IsOpen U) :
    U ⊆ stableWallEventLocus d ℳ p ℒ H h B K b ↔
      (∀ Q ∈ U, ∀ c : B.active K, Q ∉ (B.wall c).support) ∧
      IsLocallyConstant (fun Q : U =>
        cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q.val) := by
  constructor
  · intro hsub
    refine ⟨fun Q hQ => ((mem_stableWallEventLocus _ _ _ _ _ _ _ _ _ _).mp (hsub hQ)).1,
      (IsLocallyConstant.iff_eventually_eq _).mpr ?_⟩
    intro Q
    exact (continuous_subtype_val.tendsto Q).eventually
      ((mem_stableWallEventLocus _ _ _ _ _ _ _ _ _ _).mp (hsub Q.property)).2
  · rintro ⟨hallow, hlocal⟩ Q hQ
    apply (mem_stableWallEventLocus _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨hallow Q hQ, ?_⟩
    have heq := hlocal.eventually_eq (⟨Q, hQ⟩ : U)
    exact (hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨Q, hQ⟩).ge heq

/-- Finite intrinsic stability is dense for every diagram and incoming
coefficient. Rational complete-type domains and finite wall geometry suffice;
no probe, consistency, or comparison data are used. -/
theorem dense_stableWallEventLocus (K : ℕ)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0) :
    Dense (stableWallEventLocus d ℳ p ℒ H h B K b) := by
  classical
  let := h.finiteDimensional
  let W := B.activeSupport K
  let f := fun e : WallEvent (B.active K) => WallEvent.normal e (B.activeNormal K)
  let c := fun e : WallEvent (B.active K) => WallEvent.offset e (B.activeOffset K)
  let P := fun e : WallEvent (B.active K) => WallEvent.support e W
  let T := fun e : WallEvent (B.active K) =>
    wallEventPropagation d ℳ p ℒ H h B K K (Nat.le_refl K) e
  let w := fun n : Γ => ρ (p + n)
  let Types := PathDecoratedType (Q := Quiver.SingleObj (WallEvent (B.active K)))
    (fun e => T e) (fun _ => (d.shiftedQuotientGrading ℳ p K).piece) 0 b
    (wallEventPaths d ℒ H h B K K) (fun _ n => i (w n)) (fun e => f e) (fun e => Prod.snd e)
  have hW (a : B.active K) : IsRationalNormalPolyhedron h (W a) :=
    (B.wall a).rational_support
  obtain ⟨J, hJ, S, hS, hUnion⟩ := exists_finite_singularSupport_polyhedra W hW
  let := hJ
  have hf (e : WallEvent (B.active K)) : Toric.IsRationalFunctional h (f e).toLinearMap :=
    B.isRationalFunctional_wallEventNormal K e
  have hP (e : WallEvent (B.active K)) : IsRationalSemilinear h (P e) :=
    e.isRationalSemilinear_support W fun a => (hW a).isLocallyClosedPolyhedron.isRationalSemilinear
  have hdom (t : Types) : IsRationalSemilinear h
      (admissibleBackwardDomain (Quiver.Path.reverseArrowLabels (fun e => f e) t.1.val)
        (Quiver.Path.reverseArrowLabels (fun e => c e) t.1.val)
        (Quiver.Path.Degrees.reverseVertexLabels (fun _ n => i (w n)) 0 t.1.val t.2.val)
        (Quiver.Path.reverseArrowLabels (fun e => P e) t.1.val) W
        (fun _ : Unit => singularSupport W) univ) := by
    have ht := isRationalSemilinear_pathDecoratedDomain
      (Q := Quiver.SingleObj (WallEvent (B.active K))) (ι := fun _ => Γ) 0 (fun e => f e)
      (fun e => c e) (fun e => P e) W S univ h (fun _ n => w n) (fun e => hf e) (fun e => hP e)
      hW hS (IsRationalNormalPolyhedron.univ h) t.1.val t.2.val
    convert ht using 1
    apply admissibleBackwardDomain_congr_singular
    simpa only [iUnion_const] using hUnion
  obtain ⟨A, hfrontier, _⟩ := IsRationalSemilinear.exists_membershipArrangement hdom
  obtain ⟨E, hE⟩ := exists_ray_admissibilityArrangement W
    (fun c => (B.wall c).isConvexPolyhedron)
    (fun c => (B.wall c).finrank_direction_add_one) (∅ : Finset V)
  apply (A.union E).dense_isGeneric.mono
  intro Q hQ
  obtain ⟨hA, hEQ⟩ := ExceptionalArrangement.isGeneric_union.mp hQ
  obtain ⟨y, hy, _⟩ := hE Q hEQ
  apply (mem_stableWallEventLocus d ℳ p ℒ H h B K b Q).mpr
  refine ⟨?_, ?_⟩
  · simpa only [← hy] using y.notMem
  · simp only [cutoffWallEventEvaluation_def]
    exact pathDecoratedEvaluation_eventually_eq_of_notMem_frontier _ _ _ _ _ _ _ _ _ _ _ _ _ Q
      (fun t ht => hfrontier t ht hA)

/-- The common intrinsic stable locus for a family of incoming coefficients.
Only actual allowedness and actual finite evaluation germs occur in this set. -/
def stableWallEventLocusAll
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0) : Set V :=
  ⋂ k, stableWallEventLocus d ℳ p ℒ H h B k (b k)

/-- All-order stability means finite intrinsic stability at every cutoff. -/
@[simp]
theorem mem_stableWallEventLocusAll
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0) (Q : V) :
    Q ∈ stableWallEventLocusAll d ℳ p ℒ H h B b ↔
      ∀ k, Q ∈ stableWallEventLocus d ℳ p ℒ H h B k (b k) := Set.mem_iInter

/-- The intrinsic all-order locus is Gδ; it need not be open. -/
theorem isGδ_stableWallEventLocusAll
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0) :
    IsGδ (stableWallEventLocusAll d ℳ p ℒ H h B b) :=
  IsGδ.iInter fun k => (isOpen_stableWallEventLocus d ℳ p ℒ H h B k (b k)).isGδ

/-- The common intrinsic stable locus is dense for any family of finite
incoming coefficients. This geometric density does not require coherence of
those inputs, probe comparison, or consistency of the diagram. -/
theorem dense_stableWallEventLocusAll
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0) :
    Dense (stableWallEventLocusAll d ℳ p ℒ H h B b) := by
  let := h.finiteDimensional
  exact dense_iInter_of_isOpen
    (fun k => isOpen_stableWallEventLocus d ℳ p ℒ H h B k (b k))
    (fun k => dense_stableWallEventLocus d ℳ p ℒ H h B k (b k))

end Mei.ModuleProbe
