/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Uniform
public import Mei.Geometry.Convex.Polyhedron.Rational.Generic

/-!
# Uniform generic stability of varying-chamber rays

One finite exceptional arrangement controls the actual ray fibers for all inputs
in a uniformly supported incoming linear family. Both the arrangement and the
endpoint neighborhood are chosen before the input. Nearby fibers retain the
entire encounter path and degree history, hence the whole final decoration.
Finite generation is required only of the incoming range to obtain the uniform
support; chamber modules and their gradings may be infinite and may differ.

The arrangement contains the frontiers of the complete endpoint domains,
including all wall, singular and incoming-tail constraints. Vanishing branches,
cancellation, unchanged directions and lower-dimensional domains are retained.
No admissibility of boundary paths or continuity of the fiber bijections is
asserted. The resulting uniform local constancy is suitable for comparing finite
linear families of branch sums.

We use the shared semilinear membership-arrangement theorem and the actual
ray-to-domain equivalence. The closed-family interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2), and whole-component propagation follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Filter Topology Quiver Mei.Convex

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
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "dirs(" p ", " d ")" => Path.Degrees.reverseVertexLabels v i₀ p d
local notation "D(" p ", " d ")" => admissibleBackwardDomain (Path.reverseArrowLabels ν p)
  (Path.reverseArrowLabels c p) dirs(p, d) (Path.reverseArrowLabels P p) W S C

namespace PathDecoratedRay

variable (p : Path a b) {X Y : V}

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

/-- Endpoint transport retains the whole degree history. -/
@[simp]
theorem endpointEquiv_history
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ D(p, d) ↔ Y ∈ D(p, d))
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r).1 = r.1 := by
  have he := pathDecoratedRayFiberEquiv_history T ℳ i₀ x v ν ε c P W S C p Y
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r)
  rw [endpointEquiv, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply] at he
  exact he.symm.trans (pathDecoratedRayFiberEquiv_history T ℳ i₀ x v ν ε c P W S C p X r)

/-- Endpoint transport preserves the entire final decoration. -/
@[simp↓]
theorem endpointEquiv_decoration
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ D(p, d) ↔ Y ∈ D(p, d))
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r).decoration = r.decoration := by
  simp only [decoration_def, endpointEquiv_history]

/-- Transport to the same endpoint is the identity. -/
@[simp]
theorem endpointEquiv_self
    (hXX : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ D(p, d) ↔ X ∈ D(p, d))
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXX r = r := by
  apply ext_history
  exact congrArg Subtype.val (endpointEquiv_history T ℳ i₀ x v ν ε c P W S C p hXX r)

/-- Successive endpoint transports agree with direct transport. -/
@[simp]
theorem endpointEquiv_trans {Z : V}
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ D(p, d) ↔ Y ∈ D(p, d))
    (hYZ : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      Y ∈ D(p, d) ↔ Z ∈ D(p, d))
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) :
    endpointEquiv T ℳ i₀ x v ν ε c P W S C p hYZ
        (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY r) =
      endpointEquiv T ℳ i₀ x v ν ε c P W S C p (fun d hd => (hXY d hd).trans (hYZ d hd)) r := by
  apply ext_history
  simp only [endpointEquiv_history]

/-- Reversing the endpoint membership comparisons inverts transport. -/
@[simp]
theorem endpointEquiv_symm
    (hXY : ∀ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p,
      X ∈ D(p, d) ↔ Y ∈ D(p, d)) :
    (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY).symm =
      endpointEquiv T ℳ i₀ x v ν ε c P W S C p (fun d hd => (hXY d hd).symm) := by
  apply Equiv.ext
  intro r
  apply (endpointEquiv T ℳ i₀ x v ν ε c P W S C p hXY).injective
  simp only [Equiv.apply_symm_apply, endpointEquiv_trans, endpointEquiv_self]

end PathDecoratedRay

variable {E Λ : Type*} [AddCommMonoid E] [Module R E]
  (α : E →ₗ[R] ℳ a i₀) (s : Finset (Path a b))
  [AddCommGroup Λ] {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q d => i (w q d)
local notation "VD(" p ", " d ")" => admissibleBackwardDomain (Path.reverseArrowLabels ν p)
  (Path.reverseArrowLabels c p) (Path.Degrees.reverseVertexLabels vel i₀ p d)
  (Path.reverseArrowLabels P p) W S C
local notation "Ray(" z ", " X ")" => (Σ p : (s : Type _),
  PathDecoratedRay T ℳ i₀ (α z) vel ν ε c P W S C (Subtype.val p) X)
local notation "Type(" z ")" => PathDecoratedType T ℳ i₀ (α z) s vel ν ε
local notation "input" => LinearMap.comp (Submodule.subtype (ℳ a i₀)) α

include hν hP hW hS hC in
/-- One arrangement and one ambient neighborhood preserve actual ray fibers for
all parameters in a uniformly supported incoming family. The bijections preserve
complete types; no topology or continuity of these bijections is asserted. -/
theorem exists_pathDecoratedRay_uniform_membershipArrangement
    (A : ∀ p : (s : Type _), Finset (p.val.Degrees ι))
    (hA : ∀ p d, d ∉ A p → (p.val.homogeneousHistory T ℳ d).comp input = 0) :
    ∃ B : ExceptionalArrangement V,
      (∀ p d, d ∈ A p → frontier (VD(p.val, d)) ⊆ {X | ¬ B.IsGeneric X}) ∧
      ∀ X, B.IsGeneric X → ∀ᶠ Y in 𝓝 X, ∀ z : E,
        ∃ e : Ray(z, X) ≃ Ray(z, Y),
          ∀ r, (⟨(e r).1, (e r).2.1⟩ : Type(z)) = ⟨r.1, r.2.1⟩ := by
  classical
  let Labels := Σ p : (s : Type _), (A p : Type _)
  obtain ⟨B, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement
    (fun t : Labels => isRationalSemilinear_pathDecoratedDomain
      i₀ ν c P W S C h w hν hP hW hS hC t.1.val t.2.val)
  refine ⟨B, fun p d hd => hfrontier ⟨p, ⟨d, hd⟩⟩, fun X hX => ?_⟩
  filter_upwards [hstable X hX] with Y hY
  intro z
  have hmem (p : (s : Type _)) (d : p.val.Degrees ι)
      (hd : d ∈ pathDecoratedHistorySupport T ℳ i₀ (α z) vel ν ε p.val) :
      X ∈ VD(p.val, d) ↔ Y ∈ VD(p.val, d) := by
    have hs : d ∈ p.val.historySupport T ℳ (input z) :=
      (Path.mem_historySupport ..).mpr ((mem_pathDecoratedHistorySupport ..).mp hd).1
    have ha := p.val.historySupport_subset_of_comp_eq_zero T ℳ input (A p) (hA p) z hs
    exact (hY ⟨p, ⟨d, ha⟩⟩).symm
  let e : Ray(z, X) ≃ Ray(z, Y) := Equiv.sigmaCongrRight fun p =>
    PathDecoratedRay.endpointEquiv T ℳ i₀ (α z) vel ν ε c P W S C p.val (hmem p)
  refine ⟨e, ?_⟩
  intro r
  exact congrArg (Sigma.mk r.1)
    (PathDecoratedRay.endpointEquiv_history T ℳ i₀ (α z) vel ν ε c P W S C r.1.val
      (hmem r.1) r.2)

include hν hP hW hS hC in
/-- A finitely generated incoming range has one discriminant and one neighborhood
at each generic endpoint for every input's complete actual ray fiber. -/
theorem exists_pathDecoratedRay_uniform_membershipArrangement_of_fg
    (hα : (LinearMap.range α).FG) :
    ∃ B : ExceptionalArrangement V,
      ∀ X, B.IsGeneric X → ∀ᶠ Y in 𝓝 X, ∀ z : E,
        ∃ e : Ray(z, X) ≃ Ray(z, Y),
          ∀ r, (⟨(e r).1, (e r).2.1⟩ : Type(z)) = ⟨r.1, r.2.1⟩ := by
  obtain ⟨A, hA, -⟩ := exists_uniform_pathDecoratedEvaluation_expansion
    T ℳ i₀ s vel ν ε c P W S C α hα
  obtain ⟨B, -, hB⟩ := exists_pathDecoratedRay_uniform_membershipArrangement
    T ℳ i₀ ν ε c P W S C α s h w hν hP hW hS hC A hA
  exact ⟨B, hB⟩

include hν hP hW hS hC in
/-- All weighted evaluations on a finitely generated incoming range are constant
on one ambient neighborhood of each generic endpoint. The arrangement and the
neighborhood are independent of the incoming parameter, including when some
parameters kill branches or make distinct whole decorations cancel. -/
theorem exists_pathDecoratedEvaluation_uniform_eventually_eq
    (hα : (LinearMap.range α).FG) :
    ∃ B : ExceptionalArrangement V,
      ∀ X, B.IsGeneric X → ∀ᶠ Y in 𝓝 X, ∀ z : E,
        pathDecoratedEvaluation T ℳ i₀ (α z) s vel ν ε c P W S C Y =
          pathDecoratedEvaluation T ℳ i₀ (α z) s vel ν ε c P W S C X := by
  obtain ⟨B, hB⟩ := exists_pathDecoratedRay_uniform_membershipArrangement_of_fg
    T ℳ i₀ ν ε c P W S C α s h w hν hP hW hS hC hα
  refine ⟨B, fun X hX => (hB X hX).mono fun Y hY z => ?_⟩
  obtain ⟨e, he⟩ := hY z
  let := Fintype.ofFinite Ray(z, X)
  let := Fintype.ofFinite Ray(z, Y)
  symm
  rw [pathDecoratedEvaluation_def, pathDecoratedEvaluation_def]
  apply Fintype.sum_equiv e
  intro r
  simp only [PathDecoratedRay.decoration_def]
  exact (congrArg (fun t : Type(z) => t.1.val.homogeneousHistory T ℳ t.2.val (α z))
    (he r)).symm

end Mei
