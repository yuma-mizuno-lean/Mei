/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Leading
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Leading.Generic

/-!
# The constant term of canonical simultaneous wall-event evaluation

`Mei.ModuleProbe.exists_decompose_cutoffWallEventEvaluation_eq_sum_lastChange`
decomposes every component of positive relative degree of the canonical
simultaneous wall-event evaluation into the crossings of a complete admissible
backward segment. The backward-ray recursion `Θ = b + U Θ` has a constant term `b`
as well, and that theorem omits it: it only treats `n ≠ 0`.

Here we supply the constant term. The relative-degree-zero component of the
canonical evaluation is the incoming coefficient `a` when a leading ray reaches
the endpoint and is zero otherwise; two canonical events meeting one point of
the incoming line with equal crossing sign coincide, so leading contributions
are never overcounted. The backward segment plays no role, so this term is
independent of the segment and of its incoming-germ choices.

The ingredients are the leading-ray analysis of
`Mei.decompose_cutoffDecoratedEvaluation_zero_eq_ite`, the fact that a
simultaneous event propagation fixes the constant-degree class
(`decompose_wallEventPropagation_zero`, which covers differing geometric and
coefficient cutoffs), and `WallEvent.eq_of_mem_support_of_normal_sign_eq` for
the signed separation. The recursion is that of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.Convex.AdmissibleRayRealization

variable {V ι K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {n : ℕ} {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}
  {a : Fin n → ι} {v : Fin (n + 1) → V} {S : K → Set V} {C : Set V} {Q : V}

/-- Relabel the recorded encounters of a realization by their canonical signed
events while keeping the *ambient* wall family and singular sets unchanged.
`AdmissibleRayRealization.withWallEvents` instead replaces the ambient family by
the event supports themselves. That is enough for a free-standing decorated-ray
sum, but not for a sum whose admissibility family is a fixed wall inventory, as
in the canonical simultaneous wall-event evaluation. -/
def withWallEventsAmbient
    (r : AdmissibleRayRealization (fun j => f (a j)) (fun j => c (a j)) v
      (fun j => W (a j)) W S C Q)
    (hker : ∀ b, (f b).toLinearMap.ker = (affineSpan ℝ (W b)).direction)
    (hregular : ∀ j : Fin n, r.ray (r.parameter j.succ) ∉ singularSupport W)
    (hc : ∀ b x, x ∈ W b → f b x = c b) :
    AdmissibleRayRealization (fun j => (r.wallEvents j).normal f)
      (fun j => (r.wallEvents j).offset c) v (fun j => (r.wallEvents j).support W)
      W S C Q where
  ray := r.ray
  parameter := r.parameter
  parameter_zero := r.parameter_zero
  strictAnti_parameter := r.strictAnti_parameter
  transverse j := (r.wallEvents j).normal_ne_zero_of_mem_support W f
    (by simp) (fun b hb => r.normal_ne_zero_of_mem_wallEvents hker hregular j
      ((r.mem_wallEvents j b).mpr hb))
  endpoint_eq := r.endpoint_eq
  directionAt_eq := r.directionAt_eq
  bends_recorded := r.bends_recorded
  height_eq j := (r.wallEvents j).normal_apply_of_mem_support W f c hc (by simp)
  incidence j := by simp
  avoids_walls := r.avoids_walls
  incoming := r.incoming
  avoids_singular := r.avoids_singular
  off_walls := r.off_walls

end Mei.Convex.AdmissibleRayRealization

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
  (B : DirectedDiagram (d := d) h H ι)

local notation "A" => d.shiftedLieFiltration ℒ ℳ p

omit [IsWallAnnihilating H ℳ] in
/-- A simultaneous wall event fixes the whole constant-degree class of the
coefficient quotient: unchanged-degree encounters do not contribute. The
geometric wall inventory and the coefficient quotient may use different
cutoffs; the canonical evaluation needs this case. -/
theorem decompose_wallEventPropagation_zero (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) {z : (d.shiftedLieFiltration ℒ ℳ p).quotient k}
    (hz : z ∈ (d.shiftedQuotientGrading ℳ p k).piece 0) :
    (DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece
        (wallEventPropagation d ℳ p ℒ H h B k K hkK b z) 0 :
      (d.shiftedLieFiltration ℒ ℳ p).quotient k) = z := by
  rw [wallEventPropagation_apply]
  exact d.decompose_truncatedBCHAction_same ℒ ℳ p k _ hz

omit [IsWallAnnihilating H ℳ] in
omit [IsWallAnnihilating H ℳ] in
open Classical in
/-- The constant term of the canonical simultaneous wall-event evaluation. At an
endpoint the relative-degree-zero component is the incoming coefficient when a
leading ray reaches the endpoint and is zero otherwise. This is the term `b` of
the backward-ray recursion `Θ = b + U Θ`, and unlike `U Θ` it does not depend on any
backward segment. -/
theorem decompose_cutoffWallEventEvaluation_zero_eq_ite (k : ℕ)
    (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V) (Q : V) :
    (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C Q) 0 :
      (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
      if ∃ r : CutoffDecoratedRay d (d.shiftedQuotientGrading ℳ p (k + 1)).piece
          (fun e : WallEvent (B.active (k + 1)) =>
            wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl (k + 1)) e)
          a (fun n => i (ρ (p + n)))
          (fun e => e.normal (B.activeNormal (k + 1)))
          (fun e => e.offset (B.activeOffset (k + 1))) (fun e => e.2)
          (fun e => e.support (B.activeSupport (k + 1)))
          (B.activeSupport (k + 1))
          (fun _ : Unit => singularSupport (B.activeSupport (k + 1))) C (k + 1) Q,
        Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0 then
        (a : (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) else 0 := by
  classical
  rw [cutoffWallEventEvaluation_def]
  refine decompose_cutoffDecoratedEvaluation_zero_eq_ite
    (T := fun e : WallEvent (B.active (k + 1)) =>
      wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl (k + 1)) e)
    (v := fun n => i (ρ (p + n)))
    (f := fun e => e.normal (B.activeNormal (k + 1)))
    (c := fun e => e.offset (B.activeOffset (k + 1)))
    (ε := fun e => e.2)
    (P := fun e => e.support (B.activeSupport (k + 1)))
    (W := B.activeSupport (k + 1))
    (S := fun _ : Unit => singularSupport (B.activeSupport (k + 1)))
    (C := C) (k := k + 1) (Q := Q)
    (fun e x hx => decompose_wallEventPropagation_zero d ℳ p ℒ H h B (k + 1) (k + 1)
      (Nat.le_refl (k + 1)) e hx)
    (fun e => (e.support_subset (B.activeSupport (k + 1))
      e.1.property.choose_spec).trans (Set.subset_iUnion _ _))
    (fun t _ b b' hb hb' hs hs' =>
      WallEvent.eq_of_mem_support_of_normal_sign_eq b b' (B.activeSupport (k + 1))
        (B.activeNormal (k + 1)) (i (ρ (p + 0))) hb hb' hs hs')

omit [IsWallAnnihilating H ℳ] in
/-- A leading straight realization in the canonical wall-event alphabet recovers
the incoming coefficient as the constant term of the canonical simultaneous
wall-event evaluation. The realization carries its own signed event word, so
coincident walls and unchanged-degree encounters are retained, while the
admissibility family stays the diagram's wall inventory. -/
theorem decompose_cutoffWallEventEvaluation_zero_of_realization (k : ℕ) {n : ℕ}
    {u : Fin n → B.active (k + 1)}
    (r : AdmissibleRayRealization (fun j => B.activeNormal (k + 1) (u j))
      (fun j => B.activeOffset (k + 1) (u j)) (fun _ => i (ρ (p + 0)))
      (fun j => B.activeSupport (k + 1) (u j)) (B.activeSupport (k + 1))
      (fun _ : Unit => singularSupport (B.activeSupport (k + 1))) univ Q)
    (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) :
    (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a univ Q) 0 :
      (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
      (a : (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) := by
  classical
  have hker : ∀ c : B.active (k + 1),
      (B.activeNormal (k + 1) c).toLinearMap.ker =
        (affineSpan ℝ (B.activeSupport (k + 1) c)).direction := by
    intro c
    rw [B.activeSupport_apply, (B.wall c).direction_support, B.activeNormal_apply]
    ext x
    simp only [ContinuousLinearMap.coe_coe, LinearMap.mem_ker,
      h.continuousRealCharacter_apply]
  have hc : ∀ c : B.active (k + 1), ∀ x, x ∈ B.activeSupport (k + 1) c →
      B.activeNormal (k + 1) c x = B.activeOffset (k + 1) c :=
    fun c x hx => (B.wall c).offset_eq hx
  have hreg : ∀ j : Fin n,
      r.ray (r.parameter j.succ) ∉ singularSupport (B.activeSupport (k + 1)) := by
    intro j
    exact r.avoids_singular () _
      (by simpa only [r.parameter_zero] using
        r.strictAnti_parameter.antitone (Fin.zero_le j.succ))
  have hT : ∀ e : WallEvent (B.active (k + 1)),
      ∀ x ∈ (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0,
      ((DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) e x) 0 :
        (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) = x) :=
    fun e x hx => decompose_wallEventPropagation_zero d ℳ p ℒ H h B (k + 1) (k + 1)
      (Nat.le_refl (k + 1)) e hx
  have hlead : ∀ z : Σ m, Fin m → WallEvent (B.active (k + 1)),
      (AdmissibleRayRealization (fun j => (z.2 j).normal (B.activeNormal (k + 1)))
        (fun j => (z.2 j).offset (B.activeOffset (k + 1))) (fun _ => i (ρ (p + 0)))
        (fun j => (z.2 j).support (B.activeSupport (k + 1)))
        (B.activeSupport (k + 1))
        (fun _ : Unit => singularSupport (B.activeSupport (k + 1))) univ Q) →
      (∀ j : Fin z.1,
        SignType.sign ((z.2 j).normal (B.activeNormal (k + 1)) (i (ρ (p + 0)))) = (z.2 j).2) →
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a univ Q) 0 :
        (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
        (a : (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) := by
    intro z
    obtain ⟨word, rfl⟩ := List.equivSigmaTuple.surjective z
    intro g hε
    rw [cutoffWallEventEvaluation_def]
    exact decompose_cutoffDecoratedEvaluation_zero (d := d)
      (ℳ := (d.shiftedQuotientGrading ℳ p (k + 1)).piece)
      (T := fun e : WallEvent (B.active (k + 1)) =>
        wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl (k + 1)) e)
      (a := a) (v := fun m => i (ρ (p + m)))
      (f := fun e => e.normal (B.activeNormal (k + 1)))
      (c := fun e => e.offset (B.activeOffset (k + 1)))
      (ε := fun e => e.2)
      (P := fun e => e.support (B.activeSupport (k + 1)))
      (W := B.activeSupport (k + 1))
      (S := fun _ : Unit => singularSupport (B.activeSupport (k + 1)))
      (C := univ) (k := k + 1) (Q := Q) word g hT hε
      (fun e => (e.support_subset (B.activeSupport (k + 1))
        e.1.property.choose_spec).trans (Set.subset_iUnion _ _))
      (fun t _ e e' hx hx' he he' =>
        WallEvent.eq_of_mem_support_of_normal_sign_eq e e' (B.activeSupport (k + 1))
          (B.activeNormal (k + 1)) (i (ρ (p + 0))) hx hx' he he')
  exact hlead ⟨n, r.wallEvents⟩ (r.withWallEventsAmbient hker hreg hc)
    (fun j => r.normal_sign_wallEvents j)


omit [IsWallAnnihilating H ℳ] in
/-- The constant term of the canonical simultaneous wall-event evaluation is the
incoming coefficient off one exceptional arrangement that depends only on the
active wall supports and on the incoming direction: the arrangement works at
every endpoint outside it, for every incoming coefficient. -/
theorem exists_cutoffWallEventEvaluation_zero_eq (k : ℕ) :
    ∃ arr : ExceptionalArrangement V, ∀ Q : V, arr.IsGeneric Q →
      ∀ a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0,
        (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
          (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
            (Nat.le_refl (k + 1)) a univ Q) 0 :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
          (a : (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) := by
  classical
  let := h.finiteDimensional
  have hker : ∀ c : B.active (k + 1),
      (B.activeNormal (k + 1) c).toLinearMap.ker =
        (affineSpan ℝ (B.activeSupport (k + 1) c)).direction := by
    intro c
    rw [B.activeSupport_apply, (B.wall c).direction_support, B.activeNormal_apply]
    ext x
    simp only [ContinuousLinearMap.coe_coe, LinearMap.mem_ker,
      h.continuousRealCharacter_apply]
  obtain ⟨arr, hA⟩ := exists_straightRayRealizationArrangement
    (B.activeNormal (k + 1)) (B.activeOffset (k + 1))
    (fun c => (B.wall c).isConvexPolyhedron)
    (fun c => (B.wall c).finrank_direction_add_one)
    hker (fun c x hx => (B.wall c).offset_eq hx) {i (ρ (p + 0))}
  refine ⟨arr, fun Q hQ a => ?_⟩
  obtain ⟨n, u, r, -⟩ := hA Q hQ (i (ρ (p + 0))) (Finset.mem_singleton_self _)
  exact decompose_cutoffWallEventEvaluation_zero_of_realization d ℳ p ℒ H h B k r a


omit [IsWallAnnihilating H ℳ] in
open Classical in
/-- The complete last-change recursion for the canonical simultaneous wall-event
evaluation. Every retained relative degree is either zero, where the value is the
incoming coefficient (or zero when no leading ray reaches the endpoint) and does
not depend on the backward segment, or nonzero, where it is the sum over the
canonical events of a complete admissible backward segment applied to lower
relative degrees at arbitrarily close incoming germs. This packages the constant
term supplied here together with the positive-degree decomposition. -/
theorem exists_decompose_cutoffWallEventEvaluation_eq_incoming_add_sum_lastChange
    (k : ℕ) (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V)
    {n : Γ} {x y : WallComplement ((B.activeSupport (k + 1)))}
    (e : x ⟶ y) (T : ℝ) (hTpos : 0 < T)
    (hxy : x.val - y.val = T • i (ρ (p + n)))
    (htail : ∀ s ≥ T, ∀ c : B.active (k + 1),
      y.val + s • i (ρ (p + n)) ∉ (B.wall c).support)
    (hn : n ∈ d.cutoff (k + 1)) :
    ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
      (∀ b ∈ segmentWallEvents ((B.activeNormal (k + 1))) e,
        0 < η b ∧ η b < θ) ∧
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C y.val) n :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
      if n = 0 then
        (if ∃ r : CutoffDecoratedRay d (d.shiftedQuotientGrading ℳ p (k + 1)).piece
            (fun e : WallEvent (B.active (k + 1)) =>
              wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1)
                (Nat.le_refl (k + 1)) e)
            a (fun m => i (ρ (p + m)))
            (fun e => e.normal (B.activeNormal (k + 1)))
            (fun e => e.offset (B.activeOffset (k + 1))) (fun e => e.2)
            (fun e => e.support (B.activeSupport (k + 1)))
            (B.activeSupport (k + 1))
            (fun _ : Unit => singularSupport (B.activeSupport (k + 1))) C (k + 1) y.val,
          Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0 then
          (a : (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) else 0)
      else
        ∑ b ∈ segmentWallEvents ((B.activeNormal (k + 1))) e,
          ∑ m ∈ (d.finite_cutoff (k + 1)).toFinset with
            m ≠ n ∧ n - m ∈ d.monoid ∧
              b.normal ((B.activeNormal (k + 1))) (i (ρ (p + n))) =
              b.normal ((B.activeNormal (k + 1))) (i (ρ (p + m))),
          (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
            (wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1)
              (Nat.le_refl (k + 1)) b
              (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
                (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
                  (Nat.le_refl (k + 1)) a C
                  (y.val + segmentEventParameter ((B.activeNormal (k + 1))) e T b •
                    i (ρ (p + n)) + η b • i (ρ (p + m)))) m)) n :
            (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) := by
  intro θ hθ
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨fun _ => θ / 2, fun b _ => ⟨by linarith, by linarith⟩, ?_⟩
    rw [ite_eq_left rfl]
    exact decompose_cutoffWallEventEvaluation_zero_eq_ite d ℳ p ℒ H h B k a C y.val
  · obtain ⟨η, hη, hval⟩ := exists_decompose_cutoffWallEventEvaluation_eq_sum_lastChange
      d ℳ p ℒ H h B k a C e T hTpos hxy htail hn hn0 θ hθ
    exact ⟨η, hη, by rw [ite_eq_right hn0]; exact hval⟩

end Mei.ModuleProbe
