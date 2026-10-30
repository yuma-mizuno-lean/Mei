/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.LinearAlgebra.GradedModule.History.Finite

/-!
# Decorated admissible rays for a fixed propagation itinerary

Join homogeneous coefficient histories to actual transverse affine rays. Fix the
signed propagation map at every encounter, its support and hyperplane, a source
region and a homogeneous input. A contributing ray retains its degree history
and its unique admissible geometric realization. Every segment carries the whole
homogeneous component prescribed by propagation, and all these decorations are
nonzero. The crossing signs and preservation of normal velocity are checked
against each degree history. Encounters with unchanged degree and shifts with
unchanged spatial velocity are retained.

There are finitely many contributing rays at every endpoint, even for infinite
gradings. Their weighted evaluation is a finite sum over exactly the nonzero
histories whose full geometric domain admits the endpoint. For lattice-valued
velocities and rational functionals, supports, walls, obstacles and source, these
actual decorated fibers and their weighted sums are locally constant away from a
finite exceptional arrangement. This concerns one fixed signed wall itinerary;
it does not bound the number of wall itineraries.

The construction combines `homogeneousHistorySupport` with
`Convex.admissibleRayFiberEquiv`, retaining all wall avoidance, singular avoidance
and incoming-source conditions. Endpoint parameterization follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2); whole-component decorations follow Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Definition 3.1 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : Fin n → Module.End R M) (p₀ : Γ) (a : ℳ p₀)
  (velocity : Γ → V) (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (ε : Fin n → SignType) (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

open Classical in
/-- Surviving coefficient histories compatible with the prescribed crossing
signs and preservation of normal velocity at each encounter. -/
def decoratedHistorySupport : Finset (Fin n → Γ) :=
  (homogeneousHistorySupport ℳ T (a : M)).filter fun p => ∀ j,
    f j (velocity (p j)) = f j (velocity (Fin.snoc (α := fun _ => Γ) p p₀ j.succ)) ∧
      SignType.sign (f j (velocity (p j))) = ε j

/-- Membership keeps precisely the nonzero histories satisfying both geometric
normal conditions. -/
@[simp]
theorem mem_decoratedHistorySupport (p : Fin n → Γ) :
    p ∈ decoratedHistorySupport ℳ T p₀ a velocity f ε ↔
      homogeneousHistory ℳ T p a ≠ 0 ∧ ∀ j,
        f j (velocity (p j)) = f j (velocity (Fin.snoc (α := fun _ => Γ) p p₀ j.succ)) ∧
          SignType.sign (f j (velocity (p j))) = ε j := by
  classical
  simp [decoratedHistorySupport]

/-- Zero input has no compatible surviving histories. -/
@[simp]
theorem decoratedHistorySupport_zero :
    decoratedHistorySupport ℳ T p₀ 0 velocity f ε = ∅ := by
  classical
  simp [decoratedHistorySupport]

/-- Actual admissible geometric rays decorated by surviving whole-component
histories for one fixed signed propagation itinerary. `velocity` is the negative
of forward path velocity. The incoming decoration is the specified homogeneous
input, and the incoming degree is appended to the selected output degrees. -/
abbrev DecoratedAdmissibleRay (Q : V) :=
  Σ p : (decoratedHistorySupport ℳ T p₀ a velocity f ε : Type _),
    AdmissibleRayRealization f c
      (fun j => velocity (Fin.snoc (α := fun _ => Γ) p.val p₀ j)) P W S C Q

namespace DecoratedAdmissibleRay

variable {ℳ T p₀ a velocity f c ε P W S C} {Q : V}

/-- The entire homogeneous decoration on a segment, indexed backwards from the
endpoint to the incoming tail. -/
def decoration (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
    (j : Fin (n + 1)) : M :=
  homogeneousHistoryStage ℳ T r.1.val j a

/-- The incoming decoration is exactly the given input. -/
@[simp]
theorem decoration_last (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q) :
    r.decoration (Fin.last n) = (a : M) := by
  simp [decoration]

/-- The final decoration is the history's whole output component. -/
@[simp]
theorem decoration_zero (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q) :
    r.decoration 0 = homogeneousHistory ℳ T r.1.val a := by
  simp [decoration]

/-- Every segment, including the incoming segment, has nonzero decoration. -/
theorem decoration_ne_zero (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
    (j : Fin (n + 1)) : r.decoration j ≠ 0 :=
  homogeneousHistoryStage_ne_zero ℳ T r.1.val
    ((mem_decoratedHistorySupport ℳ T p₀ a velocity f ε r.1.val).mp r.1.property).1 j

/-- Each crossing retains the entire propagated homogeneous component. -/
theorem decoration_castSucc
    (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q) (j : Fin n) :
    r.decoration j.castSucc =
      (DirectSum.decompose ℳ (T j (r.decoration j.succ)) (r.1.val j) : M) :=
  homogeneousHistoryStage_castSucc_apply ℳ T r.1.val j a

/-- A selected segment is homogeneous of its recorded degree. -/
theorem decoration_mem (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
    (j : Fin n) : r.decoration j.castSucc ∈ ℳ (r.1.val j) :=
  homogeneousHistoryStage_mem ℳ T r.1.val a j

/-- Normal velocity is preserved across every recorded encounter. -/
theorem normal_velocity_eq
    (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q) (j : Fin n) :
    f j (velocity (r.1.val j)) =
      f j (velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ j.succ)) :=
  ((mem_decoratedHistorySupport ℳ T p₀ a velocity f ε r.1.val).mp r.1.property).2 j |>.1

/-- The direction determines exactly the prescribed signed crossing. -/
theorem crossing_sign
    (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q) (j : Fin n) :
    SignType.sign (f j (velocity (r.1.val j))) = ε j :=
  ((mem_decoratedHistorySupport ℳ T p₀ a velocity f ε r.1.val).mp r.1.property).2 j |>.2

/-- A nonstationary incoming degree makes the entire negative half-line proper,
regardless of intermediate spatial velocities. -/
theorem isProperMap (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
    (hv : velocity p₀ ≠ 0) (b : ℝ) : IsProperMap (fun t : Iic b => r.2.ray t) := by
  obtain ⟨hpos, _, hr⟩ := r.2.eq_backwardRay
  apply r.2.ray.isProperMap_restrict_Iic _ b
  rw [hr, incomingDirection_backwardRay, Fin.snoc_last]
  exact hv

end DecoratedAdmissibleRay

local notation "D" Q => DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q
local notation "A" p => admissibleBackwardDomain f c
  (fun j => velocity (Fin.snoc (α := fun _ => Γ) p p₀ j)) P W S C

/-- A ray exists exactly when some nonzero homogeneous history with the prescribed
crossing signs and preserved normal velocities has an admitted endpoint.
No genericity or rationality assumption is needed. -/
theorem nonempty_decoratedAdmissibleRay_iff (Q : V) :
    Nonempty (D Q) ↔ ∃ p ∈ decoratedHistorySupport ℳ T p₀ a velocity f ε, Q ∈ A p := by
  constructor
  · rintro ⟨⟨p, r⟩⟩
    exact ⟨p.val, p.property, r.mem_admissibleBackwardDomain⟩
  · rintro ⟨p, hp, hQ⟩
    exact ⟨⟨⟨p, hp⟩, admissibleRayRealization _ _ _ _ _ _ _ _ hQ⟩⟩

/-- Zero input contributes no decorated rays, even if undecorated geometric
realizations exist. -/
instance (Q : V) : IsEmpty (DecoratedAdmissibleRay ℳ T p₀ 0 velocity f c ε P W S C Q) := by
  refine ⟨fun r => ?_⟩
  have hr := r.decoration_ne_zero (Fin.last n)
  simp at hr

/-- The finite sum of whole final decorations on the actual evaluation fiber. -/
def decoratedRayEvaluation (Q : V) : M :=
  let := Fintype.ofFinite (D Q)
  ∑ r : D Q, r.decoration 0

open Classical in
/-- Evaluate by summing exactly the surviving histories admitted by the full
geometric endpoint domain. Coincident domains retain distinct histories. -/
theorem decoratedRayEvaluation_eq_sum (Q : V) :
    decoratedRayEvaluation ℳ T p₀ a velocity f c ε P W S C Q =
      ∑ p : (decoratedHistorySupport ℳ T p₀ a velocity f ε : Type _),
        if Q ∈ A p.val then homogeneousHistory ℳ T p.val a else 0 := by
  classical
  let := Fintype.ofFinite (D Q)
  let e := admissibleRayFiberEquiv W S Q (fun _ :
    (decoratedHistorySupport ℳ T p₀ a velocity f ε : Type _) => n)
    (fun _ => f) (fun _ => c)
    (fun p j => velocity (Fin.snoc (α := fun _ => Γ) p.val p₀ j))
    (fun _ => P) (fun _ => C)
  rw [decoratedRayEvaluation]
  trans ∑ p : {p : (decoratedHistorySupport ℳ T p₀ a velocity f ε : Type _) // Q ∈ A p.val},
    homogeneousHistory ℳ T p.val.val a
  · apply Fintype.sum_equiv e
    intro r
    simp only [DecoratedAdmissibleRay.decoration_zero, e, admissibleRayFiberEquiv_apply_val]
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun p : (decoratedHistorySupport ℳ T p₀ a velocity f ε : Type _) => Q ∈ A p.val)
      (Finset.univ.filter fun p : (decoratedHistorySupport ℳ T p₀ a velocity f ε : Type _) =>
        Q ∈ A p.val) (by intro p; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun p => homogeneousHistory ℳ T p.val a)).symm

/-- Vanished input has zero weighted evaluation. -/
@[simp]
theorem decoratedRayEvaluation_zero (Q : V) :
    decoratedRayEvaluation ℳ T p₀ 0 velocity f c ε P W S C Q = 0 := by
  classical
  simp [decoratedRayEvaluation]

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) [Finite J] [Finite K]
  (w : Γ → Λ)
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

include hf hP hW hS hC

/-- Outside a finite exceptional arrangement, the actual decorated fibers have
nearby history-preserving bijections. The arrangement contains every retained
domain frontier. Hence their whole weighted evaluations agree, including when
different histories have the same spatial directions. -/
theorem exists_decoratedAdmissibleRay_membershipArrangement :
    ∃ E : ExceptionalArrangement V,
      (∀ p : (decoratedHistorySupport ℳ T p₀ a (fun p => i (w p)) f ε : Type _),
        frontier (admissibleBackwardDomain f c
          (fun j => i (w (Fin.snoc (α := fun _ => Γ) p.val p₀ j))) P W S C) ⊆
            {Q | ¬ E.IsGeneric Q}) ∧
      ∀ Q, E.IsGeneric Q → ∀ᶠ Q' in nhds Q,
      ∃ e : DecoratedAdmissibleRay ℳ T p₀ a (fun p => i (w p)) f c ε P W S C Q ≃
          DecoratedAdmissibleRay ℳ T p₀ a (fun p => i (w p)) f c ε P W S C Q',
        (∀ r, (e r).1 = r.1) ∧
          decoratedRayEvaluation ℳ T p₀ a (fun p => i (w p)) f c ε P W S C Q =
            decoratedRayEvaluation ℳ T p₀ a (fun p => i (w p)) f c ε P W S C Q' := by
  classical
  obtain ⟨E, hfrontier, hE⟩ := exists_admissibleRayFiber_membershipArrangement W S
    (fun _ : (decoratedHistorySupport ℳ T p₀ a (fun p => i (w p)) f ε : Type _) => n)
    (fun _ => f) (fun _ => c) (fun _ => P) (fun _ => C)
    (fun p j => w (Fin.snoc (α := fun _ => Γ) p.val p₀ j))
    (fun _ => hf) (fun _ => hP) hW hS (fun _ => hC)
  refine ⟨E, hfrontier, fun Q hQ => (hE Q hQ).mono fun Q' hQQ' => ?_⟩
  obtain ⟨e, he⟩ := hQQ'
  refine ⟨e, he, ?_⟩
  let := Fintype.ofFinite
    (DecoratedAdmissibleRay ℳ T p₀ a (fun p => i (w p)) f c ε P W S C Q)
  let := Fintype.ofFinite
    (DecoratedAdmissibleRay ℳ T p₀ a (fun p => i (w p)) f c ε P W S C Q')
  exact Fintype.sum_equiv e _ _ fun r => by
    simp only [DecoratedAdmissibleRay.decoration_zero, he]

end Rational

end Mei
