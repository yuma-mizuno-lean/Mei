/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.BigOperators.Group.Finset.Subtype
public import Mei.Combinatorics.Quiver.Path.Labels
public import Mei.LinearAlgebra.GradedModule.History.Path.Labels
public import Mei.Geometry.Convex.Sweep.Admissible.Limit

/-!
# Decorated rays through different chamber modules

A quiver path records encounters between chambers with independently graded
semimodules. Its complete component history prescribes the direction of every
segment in a common developed affine space. Surviving histories with conserved
normal velocities and the prescribed crossing signs decorate the existing
admissible ray realizations. Thus all unrecorded-wall, singular-avoidance and
incoming-source conditions concern the entire path, including its incoming tail.

For a fixed endpoint and complete history the ray is unique. Its weight is the
whole terminal component in the final chamber module. No identification of
chamber modules, finite degree set, positive grading or bound on degree changes
is required. Encounters with equal degrees or spatial directions are retained.
Zero incoming direction is allowed here; proper incoming half-lines require a
nonzero direction, while constant incoming sections are a separate construction.

We combine `Quiver.Path.homogeneousHistory` with `AdmissibleRayRealization`.
Whole-component propagation follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4);
backward reconstruction follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Mei.Convex Quiver

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)

local notation "dirs" => Path.Degrees.reverseVertexLabels v i₀
local notation "normals" => Path.reverseArrowLabels ν

open Classical in
/-- Complete nonzero component histories satisfying the local normal-velocity
and signed crossing rules. Each arrow is retained, even if its degrees agree. -/
def pathDecoratedHistorySupport (p : Path a b) : Finset (p.Degrees ι) :=
  (p.historySupport T ℳ x).filter fun d => ∀ j,
    (normals p) j ((dirs p d) j.castSucc) = (normals p) j ((dirs p d) j.succ) ∧
      SignType.sign ((normals p) j ((dirs p d) j.castSucc)) = p.reverseArrowLabels ε j

/-- Support membership retains exactly the nonzero whole histories obeying the
two normal conditions at every recorded encounter. -/
@[simp]
theorem mem_pathDecoratedHistorySupport (p : Path a b) (d : p.Degrees ι) :
    d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p ↔
      p.homogeneousHistory T ℳ d x ≠ 0 ∧ ∀ j,
        (normals p) j ((dirs p d) j.castSucc) = (normals p) j ((dirs p d) j.succ) ∧
          SignType.sign ((normals p) j ((dirs p d) j.castSucc)) = p.reverseArrowLabels ε j := by
  classical
  simp [pathDecoratedHistorySupport]

/-- Zero incoming coefficient leaves no surviving complete histories. -/
@[simp]
theorem pathDecoratedHistorySupport_zero (p : Path a b) :
    pathDecoratedHistorySupport T ℳ i₀ 0 v ν ε p = ∅ := by
  classical
  simp [pathDecoratedHistorySupport]

/-- Appending an encounter retains a surviving prefix, a nonzero entire output
component, and the normal-velocity and sign equations at that encounter. -/
theorem mem_pathDecoratedHistorySupport_cons {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) :
    (d, i) ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε (p.cons e) ↔
      d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p ∧
        (p.cons e).homogeneousHistory T ℳ (d, i) x ≠ 0 ∧
        ν e (v c i) = ν e (v b (Path.Degrees.terminalDegree i₀ p d)) ∧
        SignType.sign (ν e (v c i)) = ε e := by
  classical
  have hnormal :
      (∀ j, (normals (p.cons e)) j ((dirs (p.cons e) (d, i)) j.castSucc) =
          (normals (p.cons e)) j ((dirs (p.cons e) (d, i)) j.succ) ∧
        SignType.sign ((normals (p.cons e)) j ((dirs (p.cons e) (d, i)) j.castSucc)) =
          (p.cons e).reverseArrowLabels ε j) ↔
      (ν e (v c i) = ν e (v b (Path.Degrees.terminalDegree i₀ p d)) ∧
        SignType.sign (ν e (v c i)) = ε e) ∧
      ∀ j, (normals p) j ((dirs p d) j.castSucc) = (normals p) j ((dirs p d) j.succ) ∧
        SignType.sign ((normals p) j ((dirs p d) j.castSucc)) = p.reverseArrowLabels ε j := by
    -- Expose the recursive path length to split its dependent encounter tuple.
    simp only [Path.reverseArrowLabels_cons, Path.Degrees.reverseVertexLabels_cons]
    dsimp only [Path.length]
    simp only [Fin.forall_fin_succ,
      Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Path.Degrees.reverseVertexLabels_zero,
      ← Fin.succ_castSucc]
  rw [mem_pathDecoratedHistorySupport, hnormal, mem_pathDecoratedHistorySupport]
  have hprefix := p.homogeneousHistory_ne_zero_of_cons T ℳ e d i (x := x)
  tauto

variable (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "support" => pathDecoratedHistorySupport T ℳ i₀ x v ν ε

/-- An actual admissible ray with a complete whole-component history along a
fixed itinerary through possibly different chamber modules and degree types. -/
abbrev PathDecoratedRay (p : Path a b) (X : V) :=
  Σ d : (support p : Type _), AdmissibleRayRealization (normals p) (p.reverseArrowLabels c)
    (dirs p d.val) (p.reverseArrowLabels P) W S C X

/-- Actual rays are exactly the histories admitted by the full endpoint domain. -/
def pathDecoratedRayFiberEquiv (p : Path a b) (X : V) :
    PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X ≃
      {d : (support p : Type _) // X ∈ admissibleBackwardDomain (normals p)
        (p.reverseArrowLabels c) (dirs p d.val) (p.reverseArrowLabels P) W S C} :=
  admissibleRayFiberEquiv W S X (fun _ => p.length) (fun _ => normals p)
    (fun _ => p.reverseArrowLabels c) (fun d : (support p : Type _) => dirs p d.val)
    (fun _ => p.reverseArrowLabels P) (fun _ => C)

/-- Endpoint parameterization keeps the entire degree history. -/
@[simp]
theorem pathDecoratedRayFiberEquiv_history (p : Path a b) (X : V)
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    (pathDecoratedRayFiberEquiv T ℳ i₀ x v ν ε c P W S C p X r).val = r.1 := by
  rw [pathDecoratedRayFiberEquiv, admissibleRayFiberEquiv_apply_val]

namespace PathDecoratedRay

variable (p : Path a b) {X Y : V}

local notation "D(" p ", " d ")" => admissibleBackwardDomain (Path.reverseArrowLabels ν p)
  (Path.reverseArrowLabels c p) (dirs p d) (Path.reverseArrowLabels P p) W S C

/-- Move the endpoint while retaining the complete component history, whenever
membership in every surviving type domain agrees at the two endpoints. -/
def endpointEquiv
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ D(p, d) ↔ Y ∈ D(p, d)) :
    PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X ≃
      PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p Y :=
  (pathDecoratedRayFiberEquiv T ℳ i₀ x v ν ε c P W S C p X).trans
    ((Equiv.subtypeEquivRight fun d :
        (pathDecoratedHistorySupport T ℳ i₀ x v ν ε p : Type _) => hXY d.val d.property).trans
      (pathDecoratedRayFiberEquiv T ℳ i₀ x v ν ε c P W S C p Y).symm)

end PathDecoratedRay

instance (p : Path a b) (X : V) :
    Finite (PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :=
  Finite.of_equiv _ (pathDecoratedRayFiberEquiv T ℳ i₀ x v ν ε c P W S C p X).symm

instance (p : Path a b) (X : V) :
    IsEmpty (PathDecoratedRay T ℳ i₀ 0 v ν ε c P W S C p X) :=
  ⟨fun r => by
    simpa only [pathDecoratedHistorySupport_zero, Finset.notMem_empty] using r.1.property⟩

namespace PathDecoratedRay

variable {T ℳ i₀ x v ν ε c P W S C} {p : Path a b} {X : V}

/-- The complete history determines the path, its incoming tail and all
encounter parameters at a fixed endpoint. -/
theorem ext_history (r s : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X)
    (h : r.1.val = s.1.val) : r = s := by
  obtain ⟨d, r⟩ := r
  obtain ⟨e, s⟩ := s
  have he : d = e := Subtype.ext h
  subst e
  exact congrArg (Sigma.mk d) (Subsingleton.elim r s)

/-- The final whole decoration lies in the final chamber module. -/
def decoration (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) : M b :=
  p.homogeneousHistory T ℳ r.1.val x

/-- The final decoration is the entire selected terminal component. -/
@[simp]
theorem decoration_def (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    r.decoration = p.homogeneousHistory T ℳ r.1.val x := (rfl)

section EndpointTransport

variable (T ℳ i₀ x v ν ε c P W S C)

/-- Endpoint transport retains the whole degree history. -/
@[simp]
theorem endpointEquiv_history
    (p : Path a b) {X Y : V}
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C ↔
      Y ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C)
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r).1 = r.1 := by
  have he := pathDecoratedRayFiberEquiv_history T ℳ i₀ x v ν ε c P W S C p Y
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r)
  rw [endpointEquiv, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply] at he
  exact he.symm.trans (pathDecoratedRayFiberEquiv_history T ℳ i₀ x v ν ε c P W S C p X r)

/-- Endpoint transport preserves the entire final decoration. -/
@[simp↓]
theorem endpointEquiv_decoration
    (p : Path a b) {X Y : V}
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C ↔
      Y ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C)
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r).decoration = r.decoration := by
  simp only [decoration_def, endpointEquiv_history]

/-- Transport to the same endpoint is the identity. -/
@[simp]
theorem endpointEquiv_self
    (p : Path a b) {X : V}
    (hXX : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C ↔
      X ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C)
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXX r = r := by
  apply ext_history
  exact congrArg Subtype.val (endpointEquiv_history T ℳ i₀ x v ν ε c P W S C p hXX r)

/-- Successive endpoint transports agree with direct transport. -/
@[simp]
theorem endpointEquiv_trans
    (p : Path a b) {X Y Z : V}
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C ↔
      Y ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C)
    (hYZ : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      Y ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C ↔
      Z ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C)
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    endpointEquiv T ℳ i₀ x v ν ε c P W S C p hYZ
        (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r) =
      endpointEquiv T ℳ i₀ x v ν ε c P W S C p (fun d hd => (hXY d hd).trans (hYZ d hd)) r := by
  apply ext_history
  simp only [endpointEquiv_history]

/-- Reversing the endpoint membership comparisons inverts transport. -/
@[simp]
theorem endpointEquiv_symm
    (p : Path a b) {X Y : V}
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C ↔
      Y ∈ admissibleBackwardDomain (Path.reverseArrowLabels ν p)
        (p.reverseArrowLabels c) (dirs p d) (p.reverseArrowLabels P) W S C) :
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY).symm =
      endpointEquiv T ℳ i₀ x v ν ε c P W S C p (fun d hd => (hXY d hd).symm) := by
  apply Equiv.ext
  intro r
  apply (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY).injective
  simp only [Equiv.apply_symm_apply, endpointEquiv_trans, endpointEquiv_self]

end EndpointTransport

/-- A contributing path has a nonzero final whole decoration. -/
theorem decoration_ne_zero (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    r.decoration ≠ 0 :=
  ((mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε p r.1.val).mp r.1.property).1

/-- The terminal decoration is homogeneous in the degree retained by its history. -/
theorem decoration_mem (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    r.decoration ∈ ℳ b (Path.Degrees.terminalDegree i₀ p r.1.val) :=
  p.homogeneousHistory_mem_vertex (T := T) (ℳ := ℳ) r.1.val i₀ x x.property

/-- The continuous path extension agrees with the entire actual ray. -/
theorem path_eq (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    r.2.ray.toContinuousMap = backwardPath (normals p) (p.reverseArrowLabels c)
      (dirs p r.1.val) X := r.2.toContinuousMap_eq_backwardPath

end PathDecoratedRay

open Classical in
/-- Sum actual rays by their signed histories, testing the complete endpoint
constraints, including the original incoming source and all avoidance conditions. -/
theorem sum_pathDecoratedRay_eq_sum_histories (p : Path a b) (X : V) :
    (let := Fintype.ofFinite (PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X)
     ∑ r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X, r.decoration) =
      ∑ d : (support p : Type _),
        if X ∈ admissibleBackwardDomain (normals p) (p.reverseArrowLabels c)
          (dirs p d.val) (p.reverseArrowLabels P) W S C
        then p.homogeneousHistory T ℳ d.val x else 0 := by
  let := Fintype.ofFinite (PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X)
  exact Fintype.sum_eq_sum_ite_of_equiv_subtype
    (pathDecoratedRayFiberEquiv T ℳ i₀ x v ν ε c P W S C p X) _
    (fun d => p.homogeneousHistory T ℳ d.val x) fun r => by
      rw [PathDecoratedRay.decoration_def, pathDecoratedRayFiberEquiv_history]

end Mei
