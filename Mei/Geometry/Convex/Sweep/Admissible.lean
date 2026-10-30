/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Uniqueness
public import Mei.Geometry.Convex.Sweep.Singular
public import Mei.Geometry.Convex.Polyhedron.Rational.Generic

/-!
# Endpoint domains of admissible transverse rays

An admissible realization records an actual finite affine ray and its transverse
encounter parameters. Its local directions and incidences determine the entire
ray. Requiring all unrecorded wall encounters to be absent, the negative half-line
to avoid singular sets, the endpoint to miss the walls, and the incoming tail to
lie eventually in its source gives exactly `admissibleBackwardDomain`.

Consequently the realizations of a fixed itinerary at an endpoint form a
subsingleton. For finitely many itineraries their disjoint union has finite
evaluation fibers. For rational-normal walls, singular sets and sources, with
lattice directions, the admitted labels are locally constant off a finite
exceptional arrangement. No genericity is required for the fiber identification.
Zero incoming directions and encounters with unchanged direction are retained;
properness and coefficient propagation are separate conditions.

The construction combines `eq_backwardRay_of_encounters` with the full-path
characterizations of the avoidance and incoming domains. The geometric
parameterization follows Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg
models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set Filter

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V)
  (W : J → Set V) (S : K → Set V) (C : Set V)

/-- The complete geometric endpoint constraints: selected incidences, absence of
unrecorded wall encounters, incoming-source admission, singular avoidance and
an endpoint off every wall. -/
def admissibleBackwardDomain : Set V :=
  (backwardAvoidanceDomain f c (fun j => v j.castSucc) P W ∩
    backwardIncomingDomain f c (fun j => v j.castSucc) P (v (Fin.last n)) C W) ∩
      backwardSingularAvoidanceDomain f c v P S ∩ {Q | ∀ a, Q ∉ W a}

/-- The endpoint domain is the intersection of the wall-avoidance, incoming-source
and singular-avoidance domains with the endpoints off every wall. -/
@[simp]
theorem mem_admissibleBackwardDomain (Q : V) :
    Q ∈ admissibleBackwardDomain f c v P W S C ↔
      Q ∈ backwardAvoidanceDomain f c (fun j => v j.castSucc) P W ∧
      Q ∈ backwardIncomingDomain f c (fun j => v j.castSucc) P (v (Fin.last n)) C W ∧
      Q ∈ backwardSingularAvoidanceDomain f c v P S ∧ ∀ a, Q ∉ W a := by
  simp only [admissibleBackwardDomain, mem_inter_iff, mem_ofPred_eq, and_assoc]

/-- Admissible endpoints satisfy the selected support and positive-time constraints. -/
theorem admissibleBackwardDomain_subset_backwardDomain :
    admissibleBackwardDomain f c v P W S C ⊆
      backwardDomain f c (fun j => v j.castSucc) P :=
  fun _ h => backwardAvoidanceDomain_subset_backwardDomain _ _ _ _ _ h.1.1.1

section Characterization

variable (Q : V) (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q)

/-- Membership in the endpoint domain is exactly the geometric conditions on the
continuous realized half-line, including time zero in singular avoidance. -/
theorem mem_admissibleBackwardDomain_iff :
    Q ∈ admissibleBackwardDomain f c v P W S C ↔
      (∀ j : Fin n, backwardRay f c v Q hpos
        (backwardParameter f c (fun j => v j.castSucc) j.succ Q) ∈ P j) ∧
      (∀ a t, t < 0 →
        (∀ j : Fin n, t ≠ backwardParameter f c (fun j => v j.castSucc) j.succ Q) →
          backwardRay f c v Q hpos t ∉ W a) ∧
      (∀ᶠ t : ℝ in atBot, backwardRay f c v Q hpos t ∈ C) ∧
      (∀ a t, t ≤ 0 → backwardRay f c v Q hpos t ∉ S a) ∧ ∀ a, Q ∉ W a := by
  have hw := mem_backwardAvoidanceDomain_inter_incoming_iff f c v Q hpos P W C
  have hs := mem_backwardSingularAvoidanceDomain_iff f c v P S Q hpos
  simp only [admissibleBackwardDomain, mem_inter_iff, mem_ofPred_eq, hw, hs]
  tauto

end Characterization

variable (Q : V)

/-- An actual transverse ray with all wall encounters recorded. Directions are
the negatives of forward velocities. The conditions prescribe local encounters,
not backward formulas. The last direction describes the incoming half-line. -/
structure AdmissibleRayRealization where
  /-- The finite affine path, including its incoming tail. -/
  ray : FiniteAffineRay V V
  /-- The endpoint followed by the encounter parameters, in backward order. -/
  parameter : Fin (n + 1) → ℝ
  /-- Time zero is the endpoint parameter. -/
  parameter_zero : parameter 0 = 0
  /-- Distinct encounters precede each other strictly. -/
  strictAnti_parameter : StrictAnti parameter
  /-- Each selected normal is transverse to its adjacent finite segment. -/
  transverse : ∀ j, f j (v j.castSucc) ≠ 0
  /-- The specified endpoint is attained. -/
  endpoint_eq : ray.endpoint = Q
  /-- Incoming directions at all recorded parameters are prescribed. -/
  directionAt_eq : ∀ j, ray.directionAt (parameter j) = v j
  /-- Every actual bend occurs at a recorded encounter. -/
  bends_recorded : ∀ t ∈ ray.bends.support, ∃ j : Fin n, t = parameter j.succ
  /-- The selected encounters lie on their hyperplanes. -/
  height_eq : ∀ j, f j (ray (parameter j.succ)) = c j
  /-- The encounter lies in the selected support. -/
  incidence : ∀ j, ray (parameter j.succ) ∈ P j
  /-- There are no additional negative-time wall encounters. -/
  avoids_walls : ∀ a t, t < 0 → (∀ j : Fin n, t ≠ parameter j.succ) → ray t ∉ W a
  /-- The incoming tail is eventually admitted by its source. -/
  incoming : ∀ᶠ t : ℝ in atBot, ray t ∈ C
  /-- The complete negative half-line misses the singular sets. -/
  avoids_singular : ∀ a t, t ≤ 0 → ray t ∉ S a
  /-- The endpoint is allowed for the wall family. -/
  off_walls : ∀ a, Q ∉ W a

namespace AdmissibleRayRealization

variable {f c v P W S C Q}

/-- Local encounter data recover the cumulative parameters and the entire ray. -/
theorem eq_backwardRay (r : AdmissibleRayRealization f c v P W S C Q) :
    ∃ hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q,
      (∀ j, r.parameter j = backwardParameter f c (fun j => v j.castSucc) j Q) ∧
        r.ray = backwardRay f c v Q hpos := by
  simpa only [r.endpoint_eq] using eq_backwardRay_of_encounters f c v r.ray r.parameter
    r.strictAnti_parameter r.bends_recorded r.parameter_zero r.directionAt_eq
    r.transverse r.height_eq

/-- At a fixed endpoint, every part of a realization is forced by its itinerary. -/
instance : Subsingleton (AdmissibleRayRealization f c v P W S C Q) where
  allEq r s := by
    obtain ⟨_, hrp, hrr⟩ := r.eq_backwardRay
    obtain ⟨_, hsp, hsr⟩ := s.eq_backwardRay
    have hp : r.parameter = s.parameter := funext fun j => (hrp j).trans (hsp j).symm
    have hr : r.ray = s.ray := hrr.trans hsr.symm
    cases r
    cases s
    congr

/-- An actual realization gives an endpoint satisfying every geometric domain
constraint. This direction needs no rationality or genericity. -/
theorem mem_admissibleBackwardDomain (r : AdmissibleRayRealization f c v P W S C Q) :
    Q ∈ admissibleBackwardDomain f c v P W S C := by
  obtain ⟨hpos, hp, hr⟩ := r.eq_backwardRay
  apply (mem_admissibleBackwardDomain_iff f c v P W S C Q hpos).mpr
  exact ⟨by simpa only [hr, hp] using r.incidence,
    by simpa only [hr, hp] using r.avoids_walls,
    by simpa only [hr] using r.incoming,
    by simpa only [hr] using r.avoids_singular, r.off_walls⟩

end AdmissibleRayRealization

/-- Realize an admissible endpoint by the unique continuous ray of its transverse
itinerary. Transversality follows from admission; no properness or nonzero
incoming direction is required. -/
def admissibleRayRealization (hQ : Q ∈ admissibleBackwardDomain f c v P W S C) :
    AdmissibleRayRealization f c v P W S C Q := by
  have hpos := fun j => ((mem_backwardDomain _ _ _ _ _).mp
    (admissibleBackwardDomain_subset_backwardDomain f c v P W S C hQ) j).1
  have hf (j) : f j (v j.castSucc) ≠ 0 := by
    intro hj
    simpa only [backwardTime_apply, hj, div_zero, lt_self_iff_false] using hpos j
  obtain ⟨hP, hW, hC, hS, hoff⟩ :=
    (mem_admissibleBackwardDomain_iff f c v P W S C Q hpos).mp hQ
  refine {
    ray := backwardRay f c v Q hpos
    parameter := fun j => backwardParameter f c (fun j => v j.castSucc) j Q
    parameter_zero := by simp
    strictAnti_parameter := strictAnti_backwardParameter _ _ _ _ hpos
    transverse := hf
    endpoint_eq := by simp
    directionAt_eq := fun j => directionAt_backwardRay_parameter _ _ _ _ _ j
    bends_recorded := ?_
    height_eq := ?_
    incidence := hP
    avoids_walls := hW
    incoming := hC
    avoids_singular := hS
    off_walls := hoff }
  · intro t ht
    rw [bends_backwardRay] at ht
    obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum t ht
    exact ⟨j, Finset.mem_singleton.mp (Finsupp.support_single_subset hj)⟩
  · intro j
    rw [backwardRay_apply_parameter]
    exact backwardPoint_height _ _ _ j (hf j) Q

/-- The constructor uses the affine cumulative encounter parameters. -/
@[simp]
theorem parameter_admissibleRayRealization
    (hQ : Q ∈ admissibleBackwardDomain f c v P W S C) (j : Fin (n + 1)) :
    (admissibleRayRealization f c v P W S C Q hQ).parameter j =
      backwardParameter f c (fun j => v j.castSucc) j Q := (rfl)

/-- The constructor uses the backward ray of its admitted endpoint. -/
@[simp]
theorem ray_admissibleRayRealization
    (hQ : Q ∈ admissibleBackwardDomain f c v P W S C) :
    (admissibleRayRealization f c v P W S C Q hQ).ray =
      backwardRay f c v Q (fun j => ((mem_backwardDomain _ _ _ _ _).mp
        (admissibleBackwardDomain_subset_backwardDomain f c v P W S C hQ) j).1) := (rfl)

/-- An itinerary is realizable at exactly the endpoints in its admissible domain.
In particular, tangent steps give empty domains, and the additional constraints
impose no hidden conditions beyond the stated continuous-path requirements. -/
@[simp]
theorem nonempty_admissibleRayRealization_iff :
    Nonempty (AdmissibleRayRealization f c v P W S C Q) ↔
      Q ∈ admissibleBackwardDomain f c v P W S C :=
  ⟨fun ⟨r⟩ => r.mem_admissibleBackwardDomain,
    fun hQ => ⟨admissibleRayRealization f c v P W S C Q hQ⟩⟩

section Rational

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i} [Finite J] [Finite K]

/-- The full admissible domain is rational semilinear for lattice directions and
rational-normal obstacles and source. Supports may be rational semilinear and
all affine offsets may be real. -/
theorem isRationalSemilinear_admissibleBackwardDomain (w : Fin (n + 1) → N)
    (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
    (hP : ∀ j, IsRationalSemilinear h (P j))
    (hW : ∀ a, IsRationalNormalPolyhedron h (W a))
    (hS : ∀ a, IsRationalNormalPolyhedron h (S a))
    (hC : IsRationalNormalPolyhedron h C) :
    IsRationalSemilinear h
      (admissibleBackwardDomain f c (fun j => i (w j)) P W S C) := by
  have hoff : IsRationalSemilinear h {Q | ∀ a, Q ∉ W a} := by
    convert IsRationalSemilinear.iInter
      (fun a => (hW a).isLocallyClosedPolyhedron.isRationalSemilinear.compl) using 1
    ext Q
    simp
  exact (((isRationalSemilinear_backwardAvoidanceDomain f c P W
    (fun j => w j.castSucc) hf hP hW).inter
    (isRationalSemilinear_backwardIncomingDomain f c P C W
      (fun j => w j.castSucc) (w (Fin.last n)) hf hP hC hW)).inter
    (isRationalSemilinear_backwardSingularAvoidanceDomain f c P S w hf hP hS)).inter hoff

end Rational

section Family

variable {H : Type*} (m : H → ℕ)
  (F : ∀ a, Fin (m a) → V →L[ℝ] ℝ) (b : ∀ a, Fin (m a) → ℝ)
  (u : ∀ a, Fin (m a + 1) → V) (A : ∀ a, Fin (m a) → Set V)
  (source : H → Set V)

/-- The actual realization fiber of a family is precisely its admitted labels.
Overlapping domains retain distinct labels, and every label has its unique ray
and encounter parameters. -/
def admissibleRayFiberEquiv :
    (Σ a, AdmissibleRayRealization (F a) (b a) (u a) (A a) W S (source a) Q) ≃
      {a // Q ∈ admissibleBackwardDomain (F a) (b a) (u a) (A a) W S (source a)} where
  toFun r := ⟨r.1, r.2.mem_admissibleBackwardDomain⟩
  invFun a := ⟨a.val, admissibleRayRealization _ _ _ _ _ _ _ _ a.property⟩
  left_inv := by
    rintro ⟨a, r⟩
    exact congrArg (Sigma.mk a) (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- Forgetting a realization keeps its itinerary label. -/
@[simp]
theorem admissibleRayFiberEquiv_apply_val
    (r : Σ a, AdmissibleRayRealization (F a) (b a) (u a) (A a) W S (source a) Q) :
    (admissibleRayFiberEquiv W S Q m F b u A source r).val = r.1 := (rfl)

/-- An admitted label is sent back to its unique backward realization. -/
@[simp]
theorem admissibleRayFiberEquiv_symm_apply
    (a : {a // Q ∈ admissibleBackwardDomain (F a) (b a) (u a) (A a) W S (source a)}) :
    (admissibleRayFiberEquiv W S Q m F b u A source).symm a =
      ⟨a.val, admissibleRayRealization _ _ _ _ _ _ _ _ a.property⟩ := (rfl)

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i} [Finite H] [Finite J] [Finite K]
  (w : ∀ a, Fin (m a + 1) → N)

/-- A finite exceptional arrangement makes the actual admissible ray fibers
locally constant by itinerary label. The domain includes all avoidance and
source constraints, so no extra admissibility assumptions are needed nearby. -/
theorem exists_admissibleRayFiber_membershipArrangement
    (hF : ∀ a j, Toric.IsRationalFunctional h (F a j).toLinearMap)
    (hA : ∀ a j, IsRationalSemilinear h (A a j))
    (hW : ∀ a, IsRationalNormalPolyhedron h (W a))
    (hS : ∀ a, IsRationalNormalPolyhedron h (S a))
    (hsource : ∀ a, IsRationalNormalPolyhedron h (source a)) :
    ∃ E : ExceptionalArrangement V,
      (∀ a, frontier (admissibleBackwardDomain (F a) (b a) (fun j => i (w a j))
        (A a) W S (source a)) ⊆ {Q | ¬ E.IsGeneric Q}) ∧
      ∀ Q, E.IsGeneric Q → ∀ᶠ Q' in nhds Q,
        ∃ e : (Σ a, AdmissibleRayRealization (F a) (b a) (fun j => i (w a j))
            (A a) W S (source a) Q) ≃
          (Σ a, AdmissibleRayRealization (F a) (b a) (fun j => i (w a j))
            (A a) W S (source a) Q'), ∀ r, (e r).1 = r.1 := by
  obtain ⟨E, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement
    (fun a => isRationalSemilinear_admissibleBackwardDomain (F a) (b a) (A a) W S
      (source a) (w a) (hF a) (hA a) hW hS (hsource a))
  refine ⟨E, hfrontier, fun Q hQ => (hstable Q hQ).mono fun Q' hQQ' => ?_⟩
  let e := Equiv.subtypeEquivRight (fun a => (hQQ' a).symm)
  refine ⟨((admissibleRayFiberEquiv W S Q m F b
    (fun a j => i (w a j)) A source).trans e).trans
    (admissibleRayFiberEquiv W S Q' m F b (fun a j => i (w a j)) A source).symm, ?_⟩
  intro r
  rfl

end Family

end Mei.Convex
