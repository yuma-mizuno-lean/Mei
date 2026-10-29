/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Rational
public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification

/-!
# Evaluation fibers of finite backward-itinerary families

For a finite collection of selected itineraries, a realization is its label and an
endpoint in its backward domain. Backward propagation uniquely determines all
encounter points and elapsed times from these data. Evaluation forgets the label.
Its fibers are finite at every endpoint, and a common locally closed rational-normal
partition makes the admitted labels, hence fiber cardinalities, constant.

Labels remain distinct when their endpoint domains overlap. Supports may be
semilinear and nonclosed; no properness or genericity hypothesis is used. These
domains impose the selected incidences and their time order. They do not impose
avoidance of additional walls or admission of an incoming tail.

The construction uses `backwardDomain`, its rationality theorem and
`IsRationalSemilinear.exists_common_partition`. The geometric parameterization by
backward propagation follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

namespace Mei.Convex

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (n : J → ℕ) (f : ∀ j, Fin (n j) → V →L[ℝ] ℝ)
  (c : ∀ j, Fin (n j) → ℝ) (v : ∀ j, Fin (n j) → V)
  (P : ∀ j, Fin (n j) → Set V)

/-- Endpoint evaluation on the disjoint union of selected backward-itinerary domains.
The itinerary label is retained in the source even when domains coincide. -/
def backwardEvaluation :
    (Σ j, backwardDomain (f j) (c j) (v j) (P j)) → V :=
  fun a => a.2.val

/-- Evaluation is the selected endpoint, independently of the itinerary label. -/
@[simp]
theorem backwardEvaluation_apply
    (a : Σ j, backwardDomain (f j) (c j) (v j) (P j)) :
    backwardEvaluation n f c v P a = a.2.val := (rfl)

/-- The evaluation fiber consists exactly of the itinerary labels admitted at the
endpoint. This counts overlapping charts with their original multiplicities. -/
def backwardEvaluationFiberEquiv (Q : V) :
    {a // backwardEvaluation n f c v P a = Q} ≃
      {j // Q ∈ backwardDomain (f j) (c j) (v j) (P j)} where
  toFun a := ⟨a.val.1, by
    simpa only [← backwardEvaluation_apply n f c v P a.val, a.property] using
      a.val.2.property⟩
  invFun j := ⟨⟨j.val, Q, j.property⟩, by simp⟩
  left_inv := by
    rintro ⟨⟨j, x, hx⟩, hQ⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hQ.symm))
  right_inv _ := rfl

/-- The fiber equivalence preserves the itinerary label. -/
@[simp]
theorem backwardEvaluationFiberEquiv_apply_val (Q : V)
    (a : {a // backwardEvaluation n f c v P a = Q}) :
    (backwardEvaluationFiberEquiv n f c v P Q a).val = a.val.1 := (rfl)

/-- The inverse fiber equivalence realizes a label at the specified endpoint. -/
@[simp]
theorem backwardEvaluationFiberEquiv_symm_apply (Q : V)
    (j : {j // Q ∈ backwardDomain (f j) (c j) (v j) (P j)}) :
    (backwardEvaluationFiberEquiv n f c v P Q).symm j =
      ⟨⟨j.val, Q, j.property⟩, by simp⟩ := (rfl)

/-- A finite family has finite evaluation fibers at every endpoint, including on
boundary strata. Rationality of the walls is unnecessary for finiteness. -/
instance [Finite J] (Q : V) : Finite {a // backwardEvaluation n f c v P a = Q} :=
  Finite.of_equiv _ (backwardEvaluationFiberEquiv n f c v P Q).symm

variable {N : Type*} [AddCommGroup N] [Finite J]
  (w : ∀ j, Fin (n j) → N) (i : N →+ V) (h : TauCeti.Toric.IsIntegralLattice i)
  (hf : ∀ j a, Toric.IsRationalFunctional h (f j a).toLinearMap)
  (hP : ∀ j a, IsRationalSemilinear h (P j a))

include hf hP

/-- Finite rational backward-itinerary families have a common locally closed
partition with label-preserving identifications of all fibers over each stratum.
Thus both the contributing labels and their multiplicities are constant there. -/
theorem exists_backwardEvaluation_stratification :
    ∃ (κ : Type) (_ : Finite κ) (C : κ → Set V),
      (∀ a, (C a).Nonempty ∧ IsLocallyClosedPolyhedron h (C a)) ∧
        (Pairwise fun a b => Disjoint (C a) (C b)) ∧ (⋃ a, C a) = Set.univ ∧
          ∀ a x, x ∈ C a → ∀ y, y ∈ C a →
            ∃ e : {z // backwardEvaluation n f c (fun j b => i (w j b)) P z = x} ≃
                {z // backwardEvaluation n f c (fun j b => i (w j b)) P z = y},
              ∀ z, (e z).val.1 = z.val.1 := by
  have hD j := isRationalSemilinear_backwardDomain
    (f j) (c j) (w j) (hf j) (hP j)
  obtain ⟨κ, hκ, C, hC, hdisj, hcover, hmem⟩ :=
    IsRationalSemilinear.exists_common_partition hD
  refine ⟨κ, hκ, C, hC, hdisj, hcover, ?_⟩
  intro a x hx y hy
  let e := Equiv.subtypeEquivRight (hmem a x hx y hy)
  refine ⟨((backwardEvaluationFiberEquiv n f c (fun j b => i (w j b)) P x).trans e).trans
    (backwardEvaluationFiberEquiv n f c (fun j b => i (w j b)) P y).symm, ?_⟩
  intro z
  simp [e]

end Mei.Convex
