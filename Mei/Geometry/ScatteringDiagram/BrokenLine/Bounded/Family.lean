/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Bounded.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Evaluation
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Charts

/-!
# Finite closed endpoint families from bounded encounter itineraries

For rational wall data and lattice velocities, the complete bounded decorated
types define one finite semilinear family. Its charts retain the full admissible
endpoint domain and original incoming source. An encounter bound on actual rays
identifies its fibers with all actual decorated rays over all finite encounter
words, and weighted evaluation sums their whole final decorations.

The domains admit finite disjoint decompositions into relative interiors of
closed rational-normal polyhedra. Each closed endpoint chart is proper over
compact endpoint sets. Boundary endpoints are retained as limits; this does
not assert admissibility of the corresponding boundary paths or classify their
degenerations. No positive grading or finite set of possible degrees is assumed.

We use `FiniteSemilinearFamily.ofDomains` and its polyhedral chart theorem.
The endpoint-family interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V J K O Λ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Λ] {i : Λ →+ V}
  (T : J → Module.End R M) (p₀ : Γ) (a : ℳ p₀)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ)
  [Finite J] [Finite K] [Finite O]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C) (L : ℕ)

local notation "vel" => fun q => i (w q)
local notation "Types" => BoundedDecoratedType ℳ T p₀ a vel f ε L
local notation "Ray(" l ", " Q ")" => DecoratedAdmissibleRay ℳ
  (fun j => T (List.get l j)) p₀ a vel
  (fun j => f (List.get l j)) (fun j => c (List.get l j))
  (fun j => ε (List.get l j)) (fun j => P (List.get l j)) W S C Q

omit [Finite J] in
include hf hP hW hS hC in
variable {ℳ T p₀ a f ε L} in
/-- The full endpoint domain of a bounded type is rational semilinear. -/
theorem BoundedDecoratedType.isRationalSemilinear_domain (t : Types) :
    IsRationalSemilinear h (t.domain c P W S C) := by
  rw [BoundedDecoratedType.domain_def]
  exact isRationalSemilinear_admissibleBackwardDomain
    (fun j => f (t.1.val.get j)) (fun j => c (t.1.val.get j))
    (fun j => P (t.1.val.get j)) W S C
    (fun j => w (Fin.snoc (α := fun _ => Γ) t.2.val p₀ j))
    (fun j => hf (t.1.val.get j)) (fun j => hP (t.1.val.get j)) hW hS hC

/-- The common finite family of all bounded complete decorated types. The
charts are inclusions of their full valid endpoint domains. -/
def boundedBrokenLineFamily : FiniteSemilinearFamily h h Types :=
  FiniteSemilinearFamily.ofDomains (BoundedDecoratedType.domain c P W S C)
    (fun t => t.isRationalSemilinear_domain c P W S C h w hf hP hW hS hC)

local notation "F" => boundedBrokenLineFamily ℳ T p₀ a f c ε P W S C h w hf hP hW hS hC L

@[simp]
theorem boundedBrokenLineFamily_domain (t : Types) :
    (F).domain t = t.domain c P W S C := FiniteSemilinearFamily.ofDomains_domain ..

@[simp]
theorem boundedBrokenLineFamily_eval (t : Types) (Q : (F).domain t) :
    (F).eval t Q = Q.val := FiniteSemilinearFamily.ofDomains_eval ..

/-- Each complete type is a finite branch; coincident domains keep distinct labels. -/
theorem boundedBrokenLineFamily_isFiniteBranch : (F).IsFiniteBranch :=
  FiniteSemilinearFamily.isFiniteBranch_ofDomains ..

instance (Q : V) : Finite ((F).fiber Q) :=
  inferInstanceAs (Finite ((FiniteSemilinearFamily.ofDomains _ _).fiber Q))

/-- An encounter bound makes the common family exhaustive for the unrestricted
actual-ray fiber, with no additional genericity assumption. -/
def boundedBrokenLineFamilyFiberEquiv (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L) :
    (F).fiber Q ≃ Σ l : List J, Ray(l, Q) :=
  (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q).trans
    (boundedDecoratedRayFiberEquiv ℳ T p₀ a vel f ε L c P W S C Q hbound).symm

local notation "e(" Q ", " hb ")" =>
  boundedBrokenLineFamilyFiberEquiv ℳ T p₀ a f c ε P W S C h w hf hP hW hS hC L Q hb

/-- Reconstructing an actual ray keeps its whole encounter word. -/
@[simp]
theorem boundedBrokenLineFamilyFiberEquiv_itinerary (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L) (z : (F).fiber Q) :
    (e(Q, hbound) z).1 = z.1.1.val := by
  unfold boundedBrokenLineFamily at *
  unfold boundedBrokenLineFamilyFiberEquiv
  rw [Equiv.trans_apply, boundedDecoratedRayFiberEquiv_symm_apply]
  simp only [FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val]

/-- Reconstruction retains the entire nonzero homogeneous degree history. -/
@[simp]
theorem boundedBrokenLineFamilyFiberEquiv_history (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L) (z : (F).fiber Q) :
    HEq (e(Q, hbound) z).2.1 z.1.2 := by
  unfold boundedBrokenLineFamily at *
  unfold boundedBrokenLineFamilyFiberEquiv
  rw [Equiv.trans_apply, boundedDecoratedRayFiberEquiv_symm_apply]
  exact (Sigma.mk.inj_iff.mp
    (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ Q z)).2

/-- Reconstruction preserves the final whole decoration. -/
@[simp↓] -- Preserve the whole decoration before expanding its component history.
theorem boundedBrokenLineFamilyFiberEquiv_decoration (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L) (z : (F).fiber Q) :
    (e(Q, hbound) z).2.decoration 0 = z.1.decoration := by
  unfold boundedBrokenLineFamily at *
  unfold boundedBrokenLineFamilyFiberEquiv
  rw [Equiv.trans_apply, boundedDecoratedRayFiberEquiv_symm_apply,
    DecoratedAdmissibleRay.decoration_zero, BoundedDecoratedType.decoration_eq]
  exact congrArg
    (fun t : Types => homogeneousHistory ℳ (fun j => T (t.1.val.get j)) t.2.val a)
    (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ Q z)

/-- Weighted evaluation is the sum over all actual encounter words, rather than
a sum over rays whose lengths have been assumed bounded in their carrier. -/
theorem boundedBrokenLineFamily_weightedEvaluation (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L) :
    (F).weightedEvaluation BoundedDecoratedType.decoration Q =
      let := Fintype.ofFinite ((F).fiber Q)
      let := Fintype.ofEquiv ((F).fiber Q) (e(Q, hbound))
      ∑ r : (Σ l : List J, Ray(l, Q)), r.2.decoration 0 := by
  classical
  let := Fintype.ofFinite ((F).fiber Q)
  let := Fintype.ofEquiv ((F).fiber Q) (e(Q, hbound))
  rw [FiniteSemilinearFamily.weightedEvaluation_def]
  exact Fintype.sum_equiv (e(Q, hbound)) _ _ fun z =>
    (boundedBrokenLineFamilyFiberEquiv_decoration
      ℳ T p₀ a f c ε P W S C h w hf hP hW hS hC L Q hbound z).symm

/-- Once both bounds exhaust actual rays, their endpoint evaluations agree.
The numerical bound changes the inventory, not the weighted sum. -/
theorem boundedBrokenLineFamily_weightedEvaluation_eq_of_bounds (L' : ℕ) (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L)
    (hbound' : ∀ (l : List J), Ray(l, Q) → l.length ≤ L') :
    (F).weightedEvaluation BoundedDecoratedType.decoration Q =
      (boundedBrokenLineFamily ℳ T p₀ a f c ε P W S C h w hf hP hW hS hC L').weightedEvaluation
        BoundedDecoratedType.decoration Q := by
  classical
  let := Fintype.ofFinite ((F).fiber Q)
  let := Fintype.ofEquiv ((F).fiber Q) (e(Q, hbound))
  rw [boundedBrokenLineFamily_weightedEvaluation ℳ T p₀ a f c ε P W S C h w
    hf hP hW hS hC L Q hbound,
    boundedBrokenLineFamily_weightedEvaluation ℳ T p₀ a f c ε P W S C h w
      hf hP hW hS hC L' Q hbound']
  -- The two inventories induce different enumerations of the same actual fiber.
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_univ]
  · intro x _
    rfl

include hf hP hW hS hC in
/-- Finite closed endpoint charts parameterize all actual rays once their
encounter bound is proved. The equivalence preserves endpoint, encounter word
and whole decoration. The closed inclusions are proper, and add only limits of
valid endpoints, without claiming boundary admissibility. -/
theorem exists_boundedBrokenLineFamily_closedCharts
    (hbound : ∀ Q (l : List J), Ray(l, Q) → l.length ≤ L) :
    ∃ (κ : Types → Type) (_ : ∀ t, Finite (κ t)) (B : ∀ t, κ t → Set V),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧
        B t j ⊆ closure (t.domain c P W S C) ∧
        IsProperMap (fun Q : B t j => (Q : V))) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = t.domain c P W S C) ∧
      ∃ e : (Σ t, Σ j : κ t, intrinsicInterior ℝ (B t j)) ≃
          (Σ Q, Σ l : List J, Ray(l, Q)),
        (∀ z, (e z).1 = z.2.2.val) ∧
        (∀ z, (e z).2.1 = z.1.1.val) ∧
        ∀ z, (e z).2.2.decoration 0 = z.1.decoration := by
  obtain ⟨κ, hκ, B, hB, hdisj, hcover, g, hgQ, hgt⟩ :=
    FiniteSemilinearFamily.exists_ofDomains_polyhedralCharts
      (BoundedDecoratedType.domain c P W S C)
      (fun t : Types => t.isRationalSemilinear_domain c P W S C h w hf hP hW hS hC)
  let e := g.trans (Equiv.sigmaCongrRight fun Q => e(Q, hbound Q))
  refine ⟨κ, hκ, B, ?_, hdisj, hcover, e, hgQ, ?_, ?_⟩
  · intro t j
    obtain ⟨hne, hp, hlc, hsub⟩ := hB t j
    exact ⟨hne, hp, hlc, hsub, hp.isClosed.isClosedEmbedding_subtypeVal.isProperMap⟩
  · intro z
    exact (boundedBrokenLineFamilyFiberEquiv_itinerary
      ℳ T p₀ a f c ε P W S C h w hf hP hW hS hC L _ _ _).trans
        (congrArg (fun t : Types => t.1.val) (hgt z))
  · intro z
    exact (boundedBrokenLineFamilyFiberEquiv_decoration
      ℳ T p₀ a f c ε P W S C h w hf hP hW hS hC L _ _ _).trans
        (congrArg BoundedDecoratedType.decoration (hgt z))

end Mei
