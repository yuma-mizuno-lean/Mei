/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison.Incoming
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison.Rays
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Evaluation
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Evaluation
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Charts

/-!
# The common endpoint family of focus-focus theta rays

The incoming and crossing charts form one `FiniteSemilinearFamily`, together
with the constant sector in zero spatial degree. Its fibers identify with the
shared incoming and single-face decorated rays and the nonzero constant section. Whole
weights recover `slabThetaEvaluation`, including at nongeneric endpoints.
Endpoint restriction retains these same global incoming records.

The construction uses the existing upper/lower slab charts and their exact
ray comparisons. It does not identify the two incoming developed charts or
assert admissibility of singular boundary paths. This is the finite endpoint
family used by the terminal matching construction, not a global resolution
certificate. The slab geometry follows Gross–Siebert, *An Invitation to Toric
Degenerations*, §§2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4).
-/

public noncomputable section

open Set AddMonoidAlgebra

namespace Mei.FocusFocus

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ)

/-- Complete chart labels, retaining incoming sides, surviving binomial indices,
and the zero-spatial-degree constant sector separately. -/
abbrev SlabThetaChartIndex := IncomingSlabChartIndex c n b ⊕ SlabChartIndex t c n ⊕ Unit

open Classical in
/-- Domains of the whole theta family. Constants are admitted everywhere exactly
when the spatial exponent is zero and the incoming coefficient is nonzero. -/
def slabThetaChartDomain : SlabThetaChartIndex t c n b → Set (ℝ × ℝ)
  | .inl α => incomingSlabDomain α.val
  | .inr (.inl α) => slabBranchDomain n (b + α.1.val.val) α.2
  | .inr (.inr _) => if (n, b) = 0 ∧ c ≠ 0 then univ else ∅

/-- Fixed whole chart weights; neither coefficient monomials nor binomial
branches with coincident endpoints are identified. -/
def slabThetaChartWeight : SlabThetaChartIndex t c n b → R[ℤ × ℤ]
  | .inl _ => single ((n.natAbs : ℤ), b) c
  | .inr (.inl α) => single (-(n.natAbs : ℤ), b + α.1.val.val)
      (c * t ^ n.natAbs * (n.natAbs.choose α.1.val.val : R))
  | .inr (.inr _) => single (0, 0) c

/-- The whole incoming or crossing path attached to a chart. In the constant
sector it is the constant path at the endpoint. These maps extend to all
endpoints; boundary paths need not be admissible. -/
def slabThetaChartPath : SlabThetaChartIndex t c n b → C(ℝ × ℝ, C(ℝ, ℝ × ℝ))
  | .inl _ => slabBranchPath n b b
  | .inr (.inl α) => slabBranchPath n (if α.2 then b + n.natAbs else b)
      (b + α.1.val.val)
  | .inr (.inr _) => slabBranchPath 0 0 0

@[simp]
theorem slabThetaChartDomain_incoming (α : IncomingSlabChartIndex c n b) :
    slabThetaChartDomain t c n b (.inl α) = incomingSlabDomain α.val := (rfl)

@[simp]
theorem slabThetaChartDomain_crossing (α : SlabChartIndex t c n) :
    slabThetaChartDomain t c n b (.inr (.inl α)) =
      slabBranchDomain n (b + α.1.val.val) α.2 := (rfl)

open Classical in
@[simp]
theorem mem_slabThetaChartDomain_constant (Q : ℝ × ℝ) (u : Unit) :
    Q ∈ slabThetaChartDomain t c n b (.inr (.inr u)) ↔ (n, b) = 0 ∧ c ≠ 0 := by
  simp [slabThetaChartDomain]

@[simp]
theorem slabThetaChartWeight_incoming (α : IncomingSlabChartIndex c n b) :
    slabThetaChartWeight t c n b (.inl α) = single ((n.natAbs : ℤ), b) c := (rfl)

@[simp]
theorem slabThetaChartWeight_crossing (α : SlabChartIndex t c n) :
    slabThetaChartWeight t c n b (.inr (.inl α)) =
      single (-(n.natAbs : ℤ), b + α.1.val.val)
        (c * t ^ n.natAbs * (n.natAbs.choose α.1.val.val : R)) := (rfl)

@[simp]
theorem slabThetaChartWeight_constant (u : Unit) :
    slabThetaChartWeight t c n b (.inr (.inr u)) = single (0, 0) c := (rfl)

@[simp]
theorem slabThetaChartPath_incoming (α : IncomingSlabChartIndex c n b) :
    slabThetaChartPath t c n b (.inl α) = slabBranchPath n b b := (rfl)

@[simp]
theorem slabThetaChartPath_crossing (α : SlabChartIndex t c n) :
    slabThetaChartPath t c n b (.inr (.inl α)) =
      slabBranchPath n (if α.2 then b + n.natAbs else b) (b + α.1.val.val) := (rfl)

@[simp]
theorem slabThetaChartPath_constant (u : Unit) (Q : ℝ × ℝ) (s : ℝ) :
    slabThetaChartPath t c n b (.inr (.inr u)) Q s = Q := by
  simp [slabThetaChartPath, slabBranchPath_apply]

/-- The incoming developed exponent retained by a complete chart. Above the
origin the crossing history uses the upper frame, including its vertical shift. -/
def slabThetaChartIncomingExponent (α : SlabThetaChartIndex t c n b) : ℤ × ℤ :=
  match α with
  | .inl _ => (n, b)
  | .inr (.inl j) => (n, if j.2 then b + n.natAbs else b)
  | .inr (.inr _) => (0, 0)

@[simp]
theorem slabThetaChartIncomingExponent_incoming (j : IncomingSlabChartIndex c n b) :
    slabThetaChartIncomingExponent t c n b (.inl j) = (n, b) := (rfl)

@[simp]
theorem slabThetaChartIncomingExponent_crossing (j : SlabChartIndex t c n) :
    slabThetaChartIncomingExponent t c n b (.inr (.inl j)) =
      (n, if j.2 then b + n.natAbs else b) := (rfl)

@[simp]
theorem slabThetaChartIncomingExponent_constant (u : Unit) :
    slabThetaChartIncomingExponent t c n b (.inr (.inr u)) = (0, 0) := (rfl)

/-- At the terminal center the whole negative half-line of every chart is its
original incoming half-line. In particular the outgoing binomial index drops
out, whereas the developed incoming exponent and the endpoint are retained. -/
theorem slabThetaChartPath_terminal (α : SlabThetaChartIndex t c n b)
    (v s : ℝ) (hs : s ≤ 0) :
    slabThetaChartPath t c n b α (0, v) s =
      (-(s * (slabThetaChartIncomingExponent t c n b α).1),
        v - s * (slabThetaChartIncomingExponent t c n b α).2) := by
  rcases α with j | j | u
  · rw [slabThetaChartPath_incoming, slabThetaChartIncomingExponent_incoming]
    exact slabBranchPath_terminal _ _ _ v s hs
  · rw [slabThetaChartPath_crossing, slabThetaChartIncomingExponent_crossing]
    exact slabBranchPath_terminal _ _ _ v s hs
  · simp only [slabThetaChartPath_constant, slabThetaChartIncomingExponent,
      Int.cast_zero, mul_zero, neg_zero, sub_zero]


/-- The whole theta evaluation is the finite sum on its admitted complete chart labels.
This combinatorial identity does not require a choice of integral lattice proof. -/
theorem slabThetaEvaluation_eq_sum_charts (Q : ℝ × ℝ) :
    slabThetaEvaluation t c n b Q =
      let := Fintype.ofFinite
        {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α}
      ∑ α : {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α},
        slabThetaChartWeight t c n b α.val := by
  classical
  let := Fintype.ofFinite
    {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α}
  let e : {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α} ≃
      {α : IncomingSlabChartIndex c n b // Q ∈ incomingSlabDomain α.val} ⊕
        {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2} ⊕
          {_u : Unit // (n, b) = 0 ∧ c ≠ 0} :=
    Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _)
      (Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _)
        (Equiv.subtypeEquivRight fun u => mem_slabThetaChartDomain_constant t c n b Q u))))
  symm
  calc
    _ = ∑ α : {α : IncomingSlabChartIndex c n b // Q ∈ incomingSlabDomain α.val} ⊕
        {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2} ⊕
          {_u : Unit // (n, b) = 0 ∧ c ≠ 0},
        Sum.elim (fun _ => single ((n.natAbs : ℤ), b) c)
          (Sum.elim (fun α => single (-(n.natAbs : ℤ), b + α.val.1.val.val)
            (c * t ^ n.natAbs * (n.natAbs.choose α.val.1.val.val : R)))
            (fun _ => single (0, 0) c)) α :=
      Fintype.sum_equiv e _ _ (fun α => by rcases α with ⟨α | α | u, hα⟩ <;> rfl)
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← incomingSlabWeightedEvaluation_eq_sum_charts,
        ← slabWeightedEvaluation_eq_sum_charts, slabThetaEvaluation_def, add_assoc]
      congr 1
      congr 1
      by_cases hn : (n, b) = 0 <;> by_cases hc : c = 0 <;> simp [hn, hc]

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- All complete chart domains are rational semilinear for the standard lattice. -/
theorem isRationalSemilinear_slabThetaChartDomain (α : SlabThetaChartIndex t c n b) :
    IsRationalSemilinear h (slabThetaChartDomain t c n b α) := by
  classical
  rcases α with α | α | α
  · exact (isLocallyClosedPolyhedron_incomingSlabDomain h α.val).isRationalSemilinear
  · exact (isLocallyClosedPolyhedron_slabBranchDomain h n (b + α.1.val.val)
      α.2).isRationalSemilinear
  · simp only [slabThetaChartDomain]
    split_ifs <;> simp

/-- The common finite endpoint family for all focus-focus theta contributions. -/
def slabThetaFamily : FiniteSemilinearFamily h h (SlabThetaChartIndex t c n b) :=
  FiniteSemilinearFamily.ofDomains (slabThetaChartDomain t c n b)
    (isRationalSemilinear_slabThetaChartDomain t c n b h)

/-- The common family is the inclusion family of its complete chart domains. -/
theorem slabThetaFamily_def : slabThetaFamily t c n b h =
    FiniteSemilinearFamily.ofDomains (slabThetaChartDomain t c n b)
      (isRationalSemilinear_slabThetaChartDomain t c n b h) := (rfl)

@[simp]
theorem slabThetaFamily_domain (α : SlabThetaChartIndex t c n b) :
    (slabThetaFamily t c n b h).domain α = slabThetaChartDomain t c n b α :=
  FiniteSemilinearFamily.ofDomains_domain ..

@[simp]
theorem slabThetaFamily_eval (α : SlabThetaChartIndex t c n b)
    (Q : (slabThetaFamily t c n b h).domain α) :
    (slabThetaFamily t c n b h).eval α Q = Q.val :=
  FiniteSemilinearFamily.ofDomains_eval ..

/-- Every chart is a finite branch, also at nongeneric endpoints. -/
theorem slabThetaFamily_isFiniteBranch : (slabThetaFamily t c n b h).IsFiniteBranch :=
  FiniteSemilinearFamily.isFiniteBranch_ofDomains ..

instance (Q : ℝ × ℝ) : Finite ((slabThetaFamily t c n b h).fiber Q) :=
  inferInstanceAs (Finite ((FiniteSemilinearFamily.ofDomains
    (slabThetaChartDomain t c n b)
    (isRationalSemilinear_slabThetaChartDomain t c n b h)).fiber Q))

/-- Exact chart comparison with actual incoming and crossing rays, including
one nonzero constant contribution in zero spatial degree. -/
private def slabThetaExplicitChartEquiv (Q : ℝ × ℝ) :
    {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α} ≃
      IncomingSlabBrokenLine c n b Q ⊕ SlabBrokenLine t c n b Q ⊕
        {_u : Unit // (n, b) = 0 ∧ c ≠ 0} := by
  classical
  refine Equiv.subtypeSum.trans (Equiv.sumCongr (incomingSlabChartEquiv c n b Q)
    (Equiv.subtypeSum.trans (Equiv.sumCongr (slabChartEquiv t c n b Q) ?_)))
  exact Equiv.subtypeEquivRight fun u => mem_slabThetaChartDomain_constant t c n b Q u

/-- Exact chart comparison with the shared empty- and one-encounter decorated
ray fibers and the nonzero stationary section. The half-plane and upper/lower
presentation labels retain complete global incoming records. -/
def slabThetaChartEquiv (Q : ℝ × ℝ) :
    {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α} ≃
      (Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q) ⊕
        (Σ upper : Bool, SlabChartRay t c n b upper Q) ⊕
          {_u : Unit // (n, b) = 0 ∧ c ≠ 0} :=
  (slabThetaExplicitChartEquiv t c n b Q).trans
    (Equiv.sumCongr (incomingSlabChartRayEquiv c n b Q).symm
      (Equiv.sumCongr (slabChartRayEquiv t c n b Q).symm (Equiv.refl _)))

/-- The shared endpoint fiber consists of the actual two ray sectors and the
nonzero constant section. -/
def slabThetaFamilyFiberEquiv (Q : ℝ × ℝ) :
    (slabThetaFamily t c n b h).fiber Q ≃
      (Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q) ⊕
        (Σ upper : Bool, SlabChartRay t c n b upper Q) ⊕
          {_u : Unit // (n, b) = 0 ∧ c ≠ 0} :=
  (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q).trans (slabThetaChartEquiv t c n b Q)

/-- The common chart equivalence retains the incoming sector. -/
@[simp]
theorem slabThetaChartEquiv_incoming (Q : ℝ × ℝ)
    (α : IncomingSlabChartIndex c n b) (hQ : Q ∈ slabThetaChartDomain t c n b (.inl α)) :
    slabThetaChartEquiv t c n b Q ⟨.inl α, hQ⟩ =
      .inl ((incomingSlabChartRayEquiv c n b Q).symm (incomingSlabChartEquiv c n b Q
        ⟨α, by simpa only [slabThetaChartDomain_incoming] using hQ⟩)) := (rfl)

/-- The common chart equivalence retains the crossing sector and branch label. -/
@[simp]
theorem slabThetaChartEquiv_crossing (Q : ℝ × ℝ)
    (α : SlabChartIndex t c n)
    (hQ : Q ∈ slabThetaChartDomain t c n b (.inr (.inl α))) :
    slabThetaChartEquiv t c n b Q ⟨.inr (.inl α), hQ⟩ =
      .inr (.inl ((slabChartRayEquiv t c n b Q).symm (slabChartEquiv t c n b Q
        ⟨α, by simpa only [slabThetaChartDomain_crossing] using hQ⟩))) := (rfl)

/-- The common chart equivalence retains the nonzero constant section. -/
@[simp]
theorem slabThetaChartEquiv_constant (Q : ℝ × ℝ) (u : Unit)
    (hQ : Q ∈ slabThetaChartDomain t c n b (.inr (.inr u))) :
    slabThetaChartEquiv t c n b Q ⟨.inr (.inr u), hQ⟩ =
      .inr (.inr ⟨u, (mem_slabThetaChartDomain_constant t c n b Q u).mp hQ⟩) := (rfl)

/-- Recover the incoming chart label from an actual incoming ray. -/
@[simp]
theorem slabThetaChartEquiv_symm_incoming_val (Q : ℝ × ℝ)
    (β : Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q) :
    ((slabThetaChartEquiv t c n b Q).symm (.inl β)).val =
      .inl ((incomingSlabChartEquiv c n b Q).symm
        (incomingSlabChartRayEquiv c n b Q β)).val := (rfl)

/-- Recover the surviving binomial branch and side from an actual crossing ray. -/
@[simp]
theorem slabThetaChartEquiv_symm_crossing_val (Q : ℝ × ℝ)
    (β : Σ upper : Bool, SlabChartRay t c n b upper Q) :
    ((slabThetaChartEquiv t c n b Q).symm (.inr (.inl β))).val =
      .inr (.inl ((slabChartEquiv t c n b Q).symm (slabChartRayEquiv t c n b Q β)).val) := (rfl)

/-- Recover the constant chart label from its section. -/
@[simp]
theorem slabThetaChartEquiv_symm_constant_val (Q : ℝ × ℝ)
    (u : {_u : Unit // (n, b) = 0 ∧ c ≠ 0}) :
    ((slabThetaChartEquiv t c n b Q).symm (.inr (.inr u))).val =
      .inr (.inr u.val) := (rfl)

/-- The endpoint fiber equivalence retains the incoming sector. -/
@[simp]
theorem slabThetaFamilyFiberEquiv_incoming (Q : ℝ × ℝ)
    (α : IncomingSlabChartIndex c n b)
    (hQ : Q ∈ (slabThetaFamily t c n b h).domain (.inl α)) :
    slabThetaFamilyFiberEquiv t c n b h Q
      ⟨.inl α, ⟨⟨Q, hQ⟩, by simp only [slabThetaFamily_eval]⟩⟩ =
        .inl ((incomingSlabChartRayEquiv c n b Q).symm (incomingSlabChartEquiv c n b Q
          ⟨α, by simpa only [slabThetaFamily_domain,
            slabThetaChartDomain_incoming] using hQ⟩)) := by
  exact (congrArg (slabThetaChartEquiv t c n b Q)
    (Subtype.ext (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ _ _))).trans
      (slabThetaChartEquiv_incoming t c n b Q α
        (by simpa only [slabThetaFamily_domain] using hQ))

/-- The endpoint fiber equivalence retains the crossing sector and branch label. -/
@[simp]
theorem slabThetaFamilyFiberEquiv_crossing (Q : ℝ × ℝ)
    (α : SlabChartIndex t c n)
    (hQ : Q ∈ (slabThetaFamily t c n b h).domain (.inr (.inl α))) :
    slabThetaFamilyFiberEquiv t c n b h Q
      ⟨.inr (.inl α), ⟨⟨Q, hQ⟩, by simp only [slabThetaFamily_eval]⟩⟩ =
        .inr (.inl ((slabChartRayEquiv t c n b Q).symm (slabChartEquiv t c n b Q
          ⟨α, by simpa only [slabThetaFamily_domain,
            slabThetaChartDomain_crossing] using hQ⟩))) := by
  exact (congrArg (slabThetaChartEquiv t c n b Q)
    (Subtype.ext (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ _ _))).trans
      (slabThetaChartEquiv_crossing t c n b Q α
        (by simpa only [slabThetaFamily_domain] using hQ))

/-- The endpoint fiber equivalence retains the nonzero constant section. -/
@[simp]
theorem slabThetaFamilyFiberEquiv_constant (Q : ℝ × ℝ) (u : Unit)
    (hQ : Q ∈ (slabThetaFamily t c n b h).domain (.inr (.inr u))) :
    slabThetaFamilyFiberEquiv t c n b h Q
      ⟨.inr (.inr u), ⟨⟨Q, hQ⟩, by simp only [slabThetaFamily_eval]⟩⟩ =
      .inr (.inr ⟨u, by simpa only [slabThetaFamily_domain,
        mem_slabThetaChartDomain_constant] using hQ⟩) := by
  exact (congrArg (slabThetaChartEquiv t c n b Q)
    (Subtype.ext (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ _ _))).trans
      (slabThetaChartEquiv_constant t c n b Q u
        (by simpa only [slabThetaFamily_domain] using hQ))

/-- Recover the incoming chart label from its point in the common endpoint fiber. -/
@[simp]
theorem slabThetaFamilyFiberEquiv_symm_incoming_fst (Q : ℝ × ℝ)
    (β : Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q) :
    ((slabThetaFamilyFiberEquiv t c n b h Q).symm (.inl β)).1 =
      .inl ((incomingSlabChartEquiv c n b Q).symm
        (incomingSlabChartRayEquiv c n b Q β)).val := by
  unfold slabThetaFamilyFiberEquiv slabThetaFamily
  simp only [Equiv.symm_trans_apply,
    FiniteSemilinearFamily.fiberOfDomainsEquiv_symm_apply_fst,
    slabThetaChartEquiv_symm_incoming_val]

/-- Recover the binomial branch and side from its point in the endpoint fiber. -/
@[simp]
theorem slabThetaFamilyFiberEquiv_symm_crossing_fst (Q : ℝ × ℝ)
    (β : Σ upper : Bool, SlabChartRay t c n b upper Q) :
    ((slabThetaFamilyFiberEquiv t c n b h Q).symm (.inr (.inl β))).1 =
      .inr (.inl ((slabChartEquiv t c n b Q).symm (slabChartRayEquiv t c n b Q β)).val) := by
  unfold slabThetaFamilyFiberEquiv slabThetaFamily
  simp only [Equiv.symm_trans_apply,
    FiniteSemilinearFamily.fiberOfDomainsEquiv_symm_apply_fst,
    slabThetaChartEquiv_symm_crossing_val]

/-- Recover the constant chart label from its point in the endpoint fiber. -/
@[simp]
theorem slabThetaFamilyFiberEquiv_symm_constant_fst (Q : ℝ × ℝ)
    (u : {_u : Unit // (n, b) = 0 ∧ c ≠ 0}) :
    ((slabThetaFamilyFiberEquiv t c n b h Q).symm (.inr (.inr u))).1 =
      .inr (.inr u.val) := by
  unfold slabThetaFamilyFiberEquiv slabThetaFamily
  simp only [Equiv.symm_trans_apply,
    FiniteSemilinearFamily.fiberOfDomainsEquiv_symm_apply_fst,
    slabThetaChartEquiv_symm_constant_val]

/-- The comparison preserves the full compact-open path, including the original
incoming tail and the developed upper/lower chart, at every admitted endpoint. -/
theorem slabThetaChartEquiv_path (Q : ℝ × ℝ)
    (α : {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α}) :
    Sum.elim (fun β => β.2.2.ray.toContinuousMap)
      (Sum.elim (fun β => β.2.val.2.ray.toContinuousMap)
        (fun _ => slabBranchPath 0 0 0 Q))
      (slabThetaChartEquiv t c n b Q α) = slabThetaChartPath t c n b α.val Q := by
  rcases α with ⟨α | α | α, hα⟩
  · have hr := incomingSlabChartRayEquiv_ray c n b Q
      ((incomingSlabChartRayEquiv c n b Q).symm
        (incomingSlabChartEquiv c n b Q ⟨α, hα⟩))
    simp only [Equiv.apply_symm_apply] at hr
    exact (congrArg FiniteAffineRay.toContinuousMap hr.symm).trans
        (incomingSlabChartEquiv c n b Q ⟨α, hα⟩).toContinuousMap_eq_slabBranchPath
  · have hr := slabChartRayEquiv_path t c n b Q
      ((slabChartRayEquiv t c n b Q).symm (slabChartEquiv t c n b Q ⟨α, hα⟩))
    simp only [Equiv.apply_symm_apply] at hr
    exact hr.symm.trans (ray_slabChartEquiv t c n b Q ⟨α, hα⟩)
  · rfl

/-- The exact shared-ray comparison carries each whole chart decoration. -/
theorem slabThetaChartEquiv_weight (Q : ℝ × ℝ)
    (α : {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α}) :
    Sum.elim (fun β => β.2.decoration 0)
      (Sum.elim (fun β => β.2.val.decoration 0) (fun _ => single (0, 0) c))
      (slabThetaChartEquiv t c n b Q α) = slabThetaChartWeight t c n b α.val := by
  rcases α with ⟨α | α | α, hα⟩
  · exact IncomingSlabChartRay.decoration_zero c n b _ Q _
  · have hw := slabChartRayEquiv_decoration t c n b Q
      ((slabChartRayEquiv t c n b Q).symm (slabChartEquiv t c n b Q ⟨α, hα⟩))
    simp only [Equiv.apply_symm_apply] at hw
    exact hw.symm.trans (decoration_slabChartEquiv t c n b Q ⟨α, hα⟩)
  · rfl

/-- The common family comparison preserves whole paths and incoming tails. -/
theorem slabThetaFamilyFiberEquiv_path (Q : ℝ × ℝ)
    (z : (slabThetaFamily t c n b h).fiber Q) :
    Sum.elim (fun β => β.2.2.ray.toContinuousMap)
      (Sum.elim (fun β => β.2.val.2.ray.toContinuousMap) (fun _ => slabBranchPath 0 0 0 Q))
      (slabThetaFamilyFiberEquiv t c n b h Q z) = slabThetaChartPath t c n b z.1 Q :=
  (slabThetaChartEquiv_path t c n b Q
    (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q z)).trans
      (congrArg (fun α => slabThetaChartPath t c n b α Q)
        (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ Q z))

/-- Common-family weights agree with the whole decorations of the actual rays. -/
theorem slabThetaFamilyFiberEquiv_weight (Q : ℝ × ℝ)
    (z : (slabThetaFamily t c n b h).fiber Q) :
    Sum.elim (fun β => β.2.decoration 0)
      (Sum.elim (fun β => β.2.val.decoration 0) (fun _ => single (0, 0) c))
      (slabThetaFamilyFiberEquiv t c n b h Q z) = slabThetaChartWeight t c n b z.1 :=
  (slabThetaChartEquiv_weight t c n b Q
    (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q z)).trans
      (congrArg (slabThetaChartWeight t c n b)
        (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ Q z))

/-- Extended paths retain their endpoints throughout each closed chart, including
terminal slab and singular-height degenerations. -/
theorem slabThetaChartPath_apply_zero (α : SlabThetaChartIndex t c n b)
    {Q : ℝ × ℝ} (hQ : Q ∈ closure (slabThetaChartDomain t c n b α)) :
    slabThetaChartPath t c n b α Q 0 = Q := by
  rcases α with α | α | α
  · simp [slabThetaChartPath_incoming, slabBranchPath_apply]
  · by_cases hn : n = 0
    · have hd : slabThetaChartDomain t c n b (.inr (.inl α)) = ∅ := by
        ext x
        simp [hn]
      simp [hd] at hQ
    · rw [slabThetaChartPath_crossing]
      exact slabBranchPath_apply_zero _ _ _ Q
        ((mem_closure_slabBranchDomain hn _ _ Q).mp hQ).1
  · exact slabThetaChartPath_constant t c n b α Q 0

/-- The complete family's boundary events are terminal slab points or, in a
crossing chart, singular-origin encounters. Constants have no boundary events. -/
theorem slabThetaChartDomain_boundary (α : SlabThetaChartIndex t c n b)
    {Q : ℝ × ℝ} (hQ : Q ∈ closure (slabThetaChartDomain t c n b α))
    (hnot : Q ∉ slabThetaChartDomain t c n b α) :
    match α with
    | .inl _ => Q.1 = 0
    | .inr (.inl j) => Q.1 = 0 ∨ Q.2 - ((b + j.1.val.val : ℤ) : ℝ) * Q.1 / n = 0
    | .inr (.inr _) => False := by
  classical
  rcases α with α | α | α
  · exact incomingSlabDomain_boundary α.val hQ hnot
  · by_cases hn : n = 0
    · have hd : slabThetaChartDomain t c n b (.inr (.inl α)) = ∅ := by
        ext x
        simp [hn]
      simp [hd] at hQ
    · exact slabBranchDomain_boundary hn (b + α.1.val.val) α.2 hQ hnot
  · simp only [slabThetaChartDomain] at hQ hnot
    split_ifs at hQ hnot <;> simp_all

/-- The extended compact-open path map is proper on the closed domain. Evaluating
at time zero recovers the endpoint, even for constant or vertical rays. -/
theorem isProperMap_slabThetaChartPath (α : SlabThetaChartIndex t c n b) :
    IsProperMap (fun Q : closure (slabThetaChartDomain t c n b α) =>
      slabThetaChartPath t c n b α Q.val) := by
  have he : (fun Q : closure (slabThetaChartDomain t c n b α) =>
      slabThetaChartPath t c n b α Q.val 0) = Subtype.val := by
    funext Q
    exact slabThetaChartPath_apply_zero t c n b α Q.property
  apply isProperMap_of_comp_of_t2
    ((slabThetaChartPath t c n b α).continuous.comp continuous_subtype_val)
    (continuous_eval_const (0 : ℝ))
  -- Composition with evaluation at zero is the closed-domain inclusion.
  change IsProperMap (fun Q : closure (slabThetaChartDomain t c n b α) =>
    slabThetaChartPath t c n b α Q.val 0)
  rw [he]
  exact isClosed_closure.isClosedEmbedding_subtypeVal.isProperMap

/-- Finite closed polyhedral charts parameterize the complete common family.
Their path maps are proper and retain the fixed incoming/crossing label even
at terminal or singular degenerations. The exact family fiber comparison then
recovers the original rays on the valid interiors. -/
theorem exists_slabThetaFamily_closedCharts :
    ∃ (κ : SlabThetaChartIndex t c n b → Type) (_ : ∀ α, Finite (κ α))
      (B : ∀ α, κ α → Set (ℝ × ℝ)),
      (∀ α j, (B α j).Nonempty ∧ IsRationalNormalPolyhedron h (B α j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B α j)) ∧
        B α j ⊆ closure (slabThetaChartDomain t c n b α) ∧
        IsProperMap (fun Q : B α j => (Q : ℝ × ℝ)) ∧
        IsProperMap (fun Q : B α j => slabThetaChartPath t c n b α Q.val)) ∧
      (∀ α, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B α j))
        (intrinsicInterior ℝ (B α l))) ∧
      (∀ α, ⋃ j, intrinsicInterior ℝ (B α j) = slabThetaChartDomain t c n b α) ∧
      ∃ e : (Σ α, Σ j : κ α, intrinsicInterior ℝ (B α j)) ≃
          (Σ Q, (slabThetaFamily t c n b h).fiber Q),
        (∀ z, (e z).1 = z.2.2.val) ∧ ∀ z, (e z).2.1 = z.1 := by
  obtain ⟨κ, hκ, B, hB, hdisj, hcover, e, he, ht⟩ :=
    FiniteSemilinearFamily.exists_ofDomains_polyhedralCharts
      (slabThetaChartDomain t c n b) (isRationalSemilinear_slabThetaChartDomain t c n b h)
  refine ⟨κ, hκ, B, ?_, hdisj, hcover, e, he, ht⟩
  intro α j
  obtain ⟨hne, hpoly, hlc, hsub⟩ := hB α j
  exact ⟨hne, hpoly, hlc, hsub, hpoly.isClosed.isClosedEmbedding_subtypeVal.isProperMap,
    (isProperMap_slabThetaChartPath t c n b α).comp
      (Topology.IsClosedEmbedding.inclusion hsub
        (hpoly.isClosed.preimage continuous_subtype_val)).isProperMap⟩

/-- Common-family evaluation is exactly the actual theta evaluation, including
constant sections and absent zero or singular crossing branches. -/
theorem slabThetaFamily_weightedEvaluation (Q : ℝ × ℝ) :
    (slabThetaFamily t c n b h).weightedEvaluation (slabThetaChartWeight t c n b) Q =
      slabThetaEvaluation t c n b Q := by
  classical
  let := Fintype.ofFinite ((FiniteSemilinearFamily.ofDomains
    (slabThetaChartDomain t c n b)
    (isRationalSemilinear_slabThetaChartDomain t c n b h)).fiber Q)
  let := Fintype.ofFinite
    {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α}
  rw [slabThetaEvaluation_eq_sum_charts, FiniteSemilinearFamily.weightedEvaluation_def]
  exact Fintype.sum_equiv (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q) _ _
    (fun z => by rw [FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val])

open Classical in
/-- Restricting endpoints does not replace or truncate incoming histories. -/
theorem slabThetaFamily_restrict_weightedEvaluation {U : Set (ℝ × ℝ)}
    (hU : IsRationalSemilinear h U) (Q : ℝ × ℝ) :
    ((slabThetaFamily t c n b h).restrict hU).weightedEvaluation
      (slabThetaChartWeight t c n b) Q =
        if Q ∈ U then slabThetaEvaluation t c n b Q else 0 := by
  calc
    _ = if Q ∈ U then (slabThetaFamily t c n b h).weightedEvaluation
        (slabThetaChartWeight t c n b) Q else 0 :=
      FiniteSemilinearFamily.weightedEvaluation_ofDomains_restrict hU _ Q
    _ = _ := by rw [slabThetaFamily_weightedEvaluation]

end Mei.FocusFocus
