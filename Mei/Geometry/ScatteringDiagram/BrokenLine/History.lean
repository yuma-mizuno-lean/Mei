/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.LinearAlgebra.GradedModule.History.Finite

/-!
# Homogeneous decorations on admissible rays

For a fixed finite encounter itinerary, attach homogeneous coefficient histories
to actual admissible transverse rays. Each segment direction is prescribed by its
degree, and each decoration is the whole component of the preceding signed
propagation map. Distinct degree histories remain distinct even when their spatial
directions coincide. Only nonzero histories contribute.

The endpoint fibers are finite without a finite grading type: their histories
belong to `homogeneousHistorySupport`, and an admissible realization is unique
for its endpoint and directions. The fibers are identified with the admitted
histories, so their weighted evaluations are sums over explicit geometric endpoint
domains. For lattice directions and rational-normal obstacles and sources, one
finite exceptional arrangement makes these actual decorated fibers, and hence
their weighted evaluations, locally constant.

This combines `homogeneousHistory` and its finite support with
`Convex.AdmissibleRayRealization` and the rational semilinear domain theorem.
The geometric and whole-component conventions follow Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2), and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definitions 3.1–3.3 (arXiv:1411.1394v2). Here the itinerary is fixed; bounds on
the set of encounter itineraries and closed degeneration charts are separate.
-/

public noncomputable section

open Set Filter

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : Fin n → Module.End R M) (p₀ : Γ) (a : ℳ p₀)
  (v : Γ → V) (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

/-- An actual admissible ray carrying a nonzero homogeneous propagation history.
The last segment is the incoming one of degree `p₀`; index zero records the
final component. All intermediate decorations are forced by `T` and `a`. -/
structure HomogeneousRayRealization (Q : V) where
  /-- The successive output degrees, in backward encounter order. -/
  history : Fin n → Γ
  /-- Vanished histories are discarded. -/
  nonzero : homogeneousHistory ℳ T history a ≠ 0
  /-- The ray and its complete admissibility data, with degree-prescribed directions. -/
  realization : Convex.AdmissibleRayRealization f c
    (Fin.snoc (fun j => v (history j)) (v p₀)) P W S C Q

namespace HomogeneousRayRealization

variable {ℳ T p₀ a v f c P W S C} {Q : V}

/-- The whole final homogeneous decoration, retaining its scalar coefficient. -/
def decoration (r : HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q) : M :=
  homogeneousHistory ℳ T r.history a

@[simp]
theorem decoration_eq (r : HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q) :
    r.decoration = homogeneousHistory ℳ T r.history a := (rfl)

/-- A contributing ray has a nonzero whole final decoration. -/
theorem decoration_ne_zero (r : HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q) :
    r.decoration ≠ 0 := r.nonzero

/-- The history determines the actual ray and its encounter parameters at a fixed endpoint. -/
@[ext]
theorem ext {r s : HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q}
    (h : r.history = s.history) : r = s := by
  cases r
  cases s
  cases h
  congr 1
  exact Subsingleton.elim _ _

end HomogeneousRayRealization

/-- The finite contributing histories admitted by the full geometric endpoint
domain. There is no genericity restriction. -/
def homogeneousRayFiberEquiv (Q : V) :
    HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q ≃
      {p : {p // p ∈ homogeneousHistorySupport ℳ T (a : M)} //
        Q ∈ Convex.admissibleBackwardDomain f c
          (Fin.snoc (fun j => v (p.val j)) (v p₀)) P W S C} where
  toFun r := ⟨⟨r.history, (mem_homogeneousHistorySupport ..).mpr r.nonzero⟩,
    r.realization.mem_admissibleBackwardDomain⟩
  invFun p := {
    history := p.val.val
    nonzero := (mem_homogeneousHistorySupport ..).mp p.val.property
    realization := Convex.admissibleRayRealization _ _ _ _ _ _ _ _ p.property }
  left_inv _ := HomogeneousRayRealization.ext rfl
  right_inv _ := rfl

/-- The endpoint-domain parameterization retains the entire degree history. -/
@[simp]
theorem homogeneousRayFiberEquiv_apply_val (Q : V)
    (r : HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q) :
    (homogeneousRayFiberEquiv ℳ T p₀ a v f c P W S C Q r).val.val = r.history := (rfl)

/-- Recovering an actual ray from an admitted history retains its degree history. -/
@[simp]
theorem homogeneousRayFiberEquiv_symm_history (Q : V)
    (p : {p : {p // p ∈ homogeneousHistorySupport ℳ T (a : M)} //
      Q ∈ Convex.admissibleBackwardDomain f c
        (Fin.snoc (fun j => v (p.val j)) (v p₀)) P W S C}) :
    ((homogeneousRayFiberEquiv ℳ T p₀ a v f c P W S C Q).symm p).history = p.val.val :=
  (rfl)

/-- A fixed endpoint has finitely many contributing decorated rays, even for an
infinite grading and without a genericity hypothesis. -/
instance (Q : V) : Finite (HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q) :=
  Finite.of_equiv _ (homogeneousRayFiberEquiv ℳ T p₀ a v f c P W S C Q).symm

/-- Zero input has no contributing ray, regardless of the geometry. -/
instance (Q : V) :
    IsEmpty (HomogeneousRayRealization ℳ T p₀ (0 : ℳ p₀) v f c P W S C Q) :=
  ⟨fun r => r.nonzero (by simp)⟩

/-- Weighted evaluation sums the whole final decorations of actual admissible rays. -/
def homogeneousRayEvaluation (Q : V) : M :=
  let := Fintype.ofFinite (HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q)
  ∑ r : HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q, r.decoration

open Classical in
/-- Weighted evaluation is the finite sum of decorations on admitted history domains.
Coincident spatial directions do not identify different degree histories. -/
theorem homogeneousRayEvaluation_eq_sum (Q : V) :
    homogeneousRayEvaluation ℳ T p₀ a v f c P W S C Q =
      ∑ p : {p // p ∈ homogeneousHistorySupport ℳ T (a : M)},
        if Q ∈ Convex.admissibleBackwardDomain f c
            (Fin.snoc (fun j => v (p.val j)) (v p₀)) P W S C
        then homogeneousHistory ℳ T p.val a else 0 := by
  let := Fintype.ofFinite (HomogeneousRayRealization ℳ T p₀ a v f c P W S C Q)
  rw [homogeneousRayEvaluation]
  calc
    _ = ∑ p : {p : {p // p ∈ homogeneousHistorySupport ℳ T (a : M)} //
        Q ∈ Convex.admissibleBackwardDomain f c
          (Fin.snoc (fun j => v (p.val j)) (v p₀)) P W S C},
        homogeneousHistory ℳ T p.val.val a :=
      Fintype.sum_equiv (homogeneousRayFiberEquiv ℳ T p₀ a v f c P W S C Q) _ _
        (fun _ => rfl)
    _ = _ := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (Finset.univ.filter fun p : {p // p ∈ homogeneousHistorySupport ℳ T (a : M)} =>
          Q ∈ Convex.admissibleBackwardDomain f c
            (Fin.snoc (fun j => v (p.val j)) (v p₀)) P W S C)
        (by simp) (fun p => homogeneousHistory ℳ T p.val a)).symm

/-- Zero incoming coefficient produces no ray and has zero weighted evaluation. -/
@[simp]
theorem homogeneousRayEvaluation_zero (Q : V) :
    homogeneousRayEvaluation ℳ T p₀ (0 : ℳ p₀) v f c P W S C Q = 0 := by
  simp [homogeneousRayEvaluation]

section Rational

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (ρ : Γ → N) [Finite J] [Finite K]

/-- Off a finite exceptional arrangement, actual decorated ray fibers are locally
identified while preserving histories and whole decorations. The arrangement also
contains every contributing history-domain frontier. -/
theorem exists_homogeneousRay_membershipArrangement
    (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
    (hP : ∀ j, IsRationalSemilinear h (P j))
    (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
    (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
    (hC : IsRationalNormalPolyhedron h C) :
    ∃ E : ExceptionalArrangement V,
      (∀ p ∈ homogeneousHistorySupport ℳ T (a : M),
        frontier (Convex.admissibleBackwardDomain f c
          (Fin.snoc (fun j => i (ρ (p j))) (i (ρ p₀))) P W S C) ⊆
            {Q | ¬ E.IsGeneric Q}) ∧
      ∀ Q, E.IsGeneric Q → ∀ᶠ Q' in nhds Q,
        ∃ e : HomogeneousRayRealization ℳ T p₀ a (fun p => i (ρ p)) f c P W S C Q ≃
          HomogeneousRayRealization ℳ T p₀ a (fun p => i (ρ p)) f c P W S C Q',
          ∀ r, (e r).history = r.history := by
  have hD (p : {p // p ∈ homogeneousHistorySupport ℳ T (a : M)}) :
      IsRationalSemilinear h (Convex.admissibleBackwardDomain f c
        (Fin.snoc (fun j => i (ρ (p.val j))) (i (ρ p₀))) P W S C) := by
    convert Convex.isRationalSemilinear_admissibleBackwardDomain f c P W S C
      (Fin.snoc (fun j => ρ (p.val j)) (ρ p₀)) hf hP hW hS hC using 1
    congr 1
    ext j
    exact Fin.lastCases (by simp) (fun j => by simp) j
  obtain ⟨E, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement hD
  refine ⟨E, fun p hp => hfrontier ⟨p, hp⟩, ?_⟩
  intro Q hQ
  exact (hstable Q hQ).mono fun Q' hQQ' => by
    let e := Equiv.subtypeEquivRight (fun p => (hQQ' p).symm)
    refine ⟨((homogeneousRayFiberEquiv ℳ T p₀ a _ f c P W S C Q).trans e).trans
      (homogeneousRayFiberEquiv ℳ T p₀ a _ f c P W S C Q').symm, fun _ => rfl⟩

/-- Finite weighted evaluation of the actual rays is locally constant away from
one finite exceptional arrangement. This holds over semirings, without additive inverses. -/
theorem exists_homogeneousRayEvaluation_eventually_eq
    (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
    (hP : ∀ j, IsRationalSemilinear h (P j))
    (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
    (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
    (hC : IsRationalNormalPolyhedron h C) :
    ∃ E : ExceptionalArrangement V, ∀ Q, E.IsGeneric Q → ∀ᶠ Q' in nhds Q,
      homogeneousRayEvaluation ℳ T p₀ a (fun p => i (ρ p)) f c P W S C Q' =
        homogeneousRayEvaluation ℳ T p₀ a (fun p => i (ρ p)) f c P W S C Q := by
  obtain ⟨E, _, hstable⟩ := exists_homogeneousRay_membershipArrangement
    ℳ T p₀ a f c P W S C h ρ hf hP hW hS hC
  refine ⟨E, fun Q hQ => (hstable Q hQ).mono fun Q' ⟨e, he⟩ => ?_⟩
  let := Fintype.ofFinite
    (HomogeneousRayRealization ℳ T p₀ a (fun p => i (ρ p)) f c P W S C Q)
  let := Fintype.ofFinite
    (HomogeneousRayRealization ℳ T p₀ a (fun p => i (ρ p)) f c P W S C Q')
  exact (Fintype.sum_equiv e _ _ (fun r => by simp [he r])).symm

end Rational

end Mei
