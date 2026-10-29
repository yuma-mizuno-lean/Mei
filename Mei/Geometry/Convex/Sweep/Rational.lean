/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Itinerary
public import Mei.Geometry.Convex.Polyhedron.Rational.LocallyClosed

/-!
# Rational endpoint domains of backward itineraries

Backward propagation toward rational-normal hyperplanes along lattice vectors has
rational linear part. The offsets may be arbitrary real numbers. Consequently,
locally closed rational-normal support constraints give locally closed rational-normal
endpoint domains, and semilinear constraints give finite disjoint decompositions into
such domains. These are the endpoint charts used to parameterize transverse affine
broken-line histories.

We use the existing `sweepProjection`, `backwardPoint` and `backwardTime` constructions,
and rational pullback and sign-cell decomposition for semilinear sets. The geometric
interpretation follows Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*,
§4 (arXiv:2205.07753v2). The constraints here impose the selected encounters and their
order; avoidance of additional walls and admission of an incoming tail are separate
conditions. Tangent steps retain the existing totalized zero-time convention.
-/

public section

namespace Mei.Convex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ι : N →+ V} {h : TauCeti.Toric.IsIntegralLattice ι}

/-- Projection along a lattice vector to a rational-normal hyperplane has rational
linear part. The formula is totalized even when the vector is tangent. -/
theorem isRationalLinearMap_sweepProjection {f : V →L[ℝ] ℝ}
    (hf : Toric.IsRationalFunctional h f.toLinearMap) (c : ℝ) (w : N) :
    Toric.IsRationalLinearMap h h
      (sweepProjection f c ((f (ι w))⁻¹ • ι w)).toAffineMap.linear := by
  rw [Toric.isRationalLinearMap_iff]
  intro g hg
  obtain ⟨a, ha⟩ := hg.exists_rat_apply w
  obtain ⟨b, hb⟩ := hf.exists_rat_apply w
  simp only [ContinuousLinearMap.coe_coe] at hb
  have he : g.comp (sweepProjection f c ((f (ι w))⁻¹ • ι w)).toAffineMap.linear =
      g - ((a / b : ℚ) : ℝ) • f.toLinearMap := by
    ext x
    simp [ha, hb, div_eq_mul_inv, mul_comm]
  rw [he]
  exact hg.sub (hf.rat_smul (a / b))

variable {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → N)
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)

include hf

/-- Every encounter point is an affine function with rational linear part of the
endpoint. No transversality or genericity hypothesis is needed for this formula. -/
theorem isRationalLinearMap_backwardPoint (j : Fin (n + 1)) :
    Toric.IsRationalLinearMap h h
      (backwardPoint f c (fun k => ι (v k)) j).toAffineMap.linear := by
  induction j using Fin.induction with
  | zero =>
    rw [backwardPoint_zero]
    exact Toric.IsRationalLinearMap.id h
  | succ j ih =>
    rw [backwardPoint_succ]
    exact (isRationalLinearMap_sweepProjection (hf j) (c j) (v j)).comp ih

/-- Elapsed time to an encounter has rational linear part as a function of the
endpoint, even with arbitrary real hyperplane offsets. -/
theorem isRationalFunctional_backwardTime (j : Fin n) :
    Toric.IsRationalFunctional h
      (backwardTime f c (fun k => ι (v k)) j).toAffineMap.linear := by
  obtain ⟨a, ha⟩ := (hf j).exists_rat_apply (v j)
  simp only [ContinuousLinearMap.coe_coe] at ha
  have hp := (isRationalLinearMap_backwardPoint f c v hf j.castSucc).map_functional (hf j)
  have he : (backwardTime f c (fun k => ι (v k)) j).toAffineMap.linear =
      ((a⁻¹ : ℚ) : ℝ) • (-(f j).toLinearMap.comp
        (backwardPoint f c (fun k => ι (v k)) j.castSucc).toAffineMap.linear) := by
    ext x
    simp [ha]
  rw [he]
  exact hp.neg.rat_smul a⁻¹

/-- Pulling back rational support inequalities gives rational endpoint conditions,
including the elapsed-time rows. -/
theorem isRationalFunctional_backwardCondition {m : Fin n → ℕ}
    (g : ∀ j, Fin (m j) → V →ᴬ[ℝ] ℝ)
    (hg : ∀ j k, Toric.IsRationalFunctional h (g j k).toAffineMap.linear)
    (a : Fin n ⊕ (Σ j, Fin (m j))) :
    Toric.IsRationalFunctional h
      (backwardCondition f c (fun k => ι (v k)) g a).toAffineMap.linear := by
  cases a with
  | inl j =>
    have he : backwardCondition f c (fun k => ι (v k)) g (.inl j) =
        -backwardTime f c (fun k => ι (v k)) j := by
      ext Q
      exact backwardCondition_time _ _ _ _ _ _
    rw [he]
    exact (isRationalFunctional_backwardTime f c v hf j).neg
  | inr a =>
    have he : backwardCondition f c (fun k => ι (v k)) g (.inr a) =
        (g a.1 a.2).comp (backwardPoint f c (fun k => ι (v k)) a.1.succ) := by
      ext Q
      exact backwardCondition_support _ _ _ _ _ _ _
    rw [he]
    exact (isRationalLinearMap_backwardPoint f c v hf a.1.succ).map_functional (hg _ _)

/-- Closed rational-normal supports give a closed rational-normal weak endpoint
domain. Zero elapsed times and tangent steps are allowed. -/
theorem isRationalNormalPolyhedron_weakBackwardDomain {P : Fin n → Set V}
    (hP : ∀ j, IsRationalNormalPolyhedron h (P j)) :
    IsRationalNormalPolyhedron h (weakBackwardDomain f c (fun k => ι (v k)) P) := by
  choose A hA using fun j => isRationalNormalPolyhedron_iff.mp (hP j)
  let g := fun j => (A j).inequality
  have he : weakBackwardDomain f c (fun k => ι (v k)) P =
      {Q | ∀ a, backwardCondition f c (fun k => ι (v k)) g a Q ≤ 0} := by
    ext Q
    simp only [mem_weakBackwardDomain, ← hA, RationalAffinePolyhedron.mem_carrier,
      Set.mem_ofPred_eq, backwardCondition_time, backwardCondition_support, Sum.forall,
      Sigma.forall, neg_nonpos, forall_and, g]
  rw [he]
  exact isRationalNormalPolyhedron_setOf_forall _
    (isRationalFunctional_backwardCondition f c v hf g (fun j => (A j).rational_linear))

/-- Locally closed rational-normal supports give a single locally closed
rational-normal endpoint domain with strictly positive elapsed times. -/
theorem isLocallyClosedPolyhedron_backwardDomain {P : Fin n → Set V}
    (hP : ∀ j, IsLocallyClosedPolyhedron h (P j)) :
    IsLocallyClosedPolyhedron h (backwardDomain f c (fun k => ι (v k)) P) := by
  have ht (j : Fin n) : IsLocallyClosedPolyhedron h
      {Q | -backwardTime f c (fun k => ι (v k)) j Q < 0} := by
    simpa using isLocallyClosedPolyhedron_setOf_forall_neg
      (fun _ : Unit => -backwardTime f c (fun k => ι (v k)) j)
      (fun _ => (isRationalFunctional_backwardTime f c v hf j).neg)
  convert IsLocallyClosedPolyhedron.iInter (fun j => (ht j).inter
    ((hP j).preimage _ (isRationalLinearMap_backwardPoint f c v hf j.succ))) using 1
  ext Q
  simp only [mem_backwardDomain, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_ofPred_eq, neg_lt_zero]

/-- Finite Boolean support constraints give semilinear endpoint domains. The
existing disjoint sign-cell decomposition therefore applies to these domains. -/
theorem isRationalSemilinear_backwardDomain {P : Fin n → Set V}
    (hP : ∀ j, IsRationalSemilinear h (P j)) :
    IsRationalSemilinear h (backwardDomain f c (fun k => ι (v k)) P) := by
  have ht (j : Fin n) : IsRationalSemilinear h
      {Q | -backwardTime f c (fun k => ι (v k)) j Q < 0} :=
    IsRationalSemilinear.setOf_neg (g := -backwardTime f c (fun k => ι (v k)) j)
      (isRationalFunctional_backwardTime f c v hf j).neg
  convert IsRationalSemilinear.iInter (fun j => (ht j).inter
    ((hP j).preimage _ (isRationalLinearMap_backwardPoint f c v hf j.succ))) using 1
  ext Q
  simp only [mem_backwardDomain, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_ofPred_eq, neg_lt_zero]

end Mei.Convex
