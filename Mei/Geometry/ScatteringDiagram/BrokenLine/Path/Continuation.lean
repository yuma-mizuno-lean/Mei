/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family

/-!
# Continuous continuation of varying-chamber decorated rays

On a set of endpoints where membership in every complete type domain of a finite path
inventory is constant, the actual rays at one endpoint continue to all others, preserving
their complete types: the endpoints and one reference fiber form a product chart of the
whole ray family over that set. Each continued ray, including its incoming tail, varies
continuously in compact-open path space, and the continuation is the only family of
type-preserving bijections.

Away from a finite exceptional arrangement containing every type-domain frontier, every
endpoint has a convex open neighborhood of this kind. Distinct types remain separate even
when their geometric paths coincide, and no admissibility of paths at the boundary of the
neighborhood is asserted.

The construction uses `PathDecoratedRay.endpointEquiv` and the backward path of each
type. The endpoint deformation viewpoint follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
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
  (s : Finset (Path a b))

local notation "Labels" => PathDecoratedType T ℳ i₀ x s v ν ε
local notation "D" => fun t : Labels => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t)))
  (Path.Degrees.reverseVertexLabels v i₀ (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C
local notation "path" => fun t : Labels => backwardPath
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t)))
  (Path.Degrees.reverseVertexLabels v i₀ (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
local notation "Rays(" X ")" => Σ p : (s : Type _),
  PathDecoratedRay T ℳ i₀ x v ν ε c P W S C (Subtype.val p) X

/-- A family of actual rays along one path with one complete history depends
continuously on its endpoints in compact-open path space, including its incoming tail. -/
theorem PathDecoratedRay.continuous_of_history_eq {X : Type*} [TopologicalSpace X]
    {p : Path a b} {Y : X → V} (r : ∀ z, PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p (Y z))
    (d : p.Degrees ι) (hY : Continuous Y) (hd : ∀ z, (r z).1.val = d) :
    Continuous (fun z => (r z).2.ray.toContinuousMap) := by
  have hpath (z : X) : (r z).2.ray.toContinuousMap = backwardPath (p.reverseArrowLabels ν)
      (p.reverseArrowLabels c) (Path.Degrees.reverseVertexLabels v i₀ p d) (Y z) := by
    rw [PathDecoratedRay.path_eq, hd z]
  simpa only [hpath, Function.comp_def] using (backwardPath _ _ _).continuous.comp hY

/-- Move every ray of the inventory to another endpoint, retaining its complete type,
whenever membership in every type domain agrees at the two endpoints. -/
def pathDecoratedRaysEndpointEquiv {X Y : V} (h : ∀ t : Labels, X ∈ D t ↔ Y ∈ D t) :
    Rays(X) ≃ Rays(Y) :=
  Equiv.sigmaCongrRight fun p => PathDecoratedRay.endpointEquiv T ℳ i₀ x v ν ε c P W S C p.val
    fun d hd => h ⟨p, ⟨d, hd⟩⟩

/-- Endpoint transport of the inventory preserves complete types. -/
@[simp]
theorem pathDecoratedRaysEndpointEquiv_type {X Y : V} (h : ∀ t : Labels, X ∈ D t ↔ Y ∈ D t)
    (r : Rays(X)) :
    (⟨(pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s h r).1,
      (pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s h r).2.1⟩ : Labels) =
      ⟨r.1, r.2.1⟩ :=
  Sigma.ext rfl (heq_of_eq (PathDecoratedRay.endpointEquiv_history T ℳ i₀ x v ν ε c P W S C
    r.1.val _ r.2))

/-- Endpoint transport of the inventory preserves the whole final decoration. -/
@[simp]
theorem pathDecoratedRaysEndpointEquiv_decoration {X Y : V}
    (h : ∀ t : Labels, X ∈ D t ↔ Y ∈ D t) (r : Rays(X)) :
    (pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s h r).2.decoration =
      r.2.decoration :=
  PathDecoratedRay.endpointEquiv_decoration T ℳ i₀ x v ν ε c P W S C r.1.val _ r.2

/-- An actual ray of the inventory is determined by its endpoint and complete type. -/
theorem pathDecoratedRays_ext {X : V} (r₁ r₂ : Rays(X))
    (h : (⟨r₁.1, r₁.2.1⟩ : Labels) = ⟨r₂.1, r₂.2.1⟩) : r₁ = r₂ := by
  obtain ⟨p, r₁⟩ := r₁
  obtain ⟨q, r₂⟩ := r₂
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp h
  exact congrArg (Sigma.mk p)
    (PathDecoratedRay.ext_history r₁ r₂ (congrArg Subtype.val (eq_of_heq hd)))

/-- A type-preserving bijection of inventory fibers is endpoint transport. -/
theorem eq_pathDecoratedRaysEndpointEquiv {X Y : V} (h : ∀ t : Labels, X ∈ D t ↔ Y ∈ D t)
    (e : Rays(X) ≃ Rays(Y)) (he : ∀ r, (⟨(e r).1, (e r).2.1⟩ : Labels) = ⟨r.1, r.2.1⟩) :
    e = pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s h :=
  Equiv.ext fun r => pathDecoratedRays_ext T ℳ i₀ x v ν ε c P W S C s _ _
    ((he r).trans (pathDecoratedRaysEndpointEquiv_type T ℳ i₀ x v ν ε c P W S C s h r).symm)

section Trivialization

variable {U : Set V} {X₀ : V}

/-- A set of endpoints with constant admitted types is a product of its endpoints and
one reference fiber. All actual rays over the set are retained. -/
def pathDecoratedFamilyTrivialization (hU : ∀ Y ∈ U, ∀ t : Labels, X₀ ∈ D t ↔ Y ∈ D t) :
    U × Rays(X₀) ≃ Σ Y : U, Rays(Y.val) :=
  (Equiv.sigmaEquivProdOfEquiv fun Y : U =>
    (pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s (hU Y Y.property)).symm).symm

/-- The chart map keeps the endpoint and continues the reference ray. -/
@[simp]
theorem pathDecoratedFamilyTrivialization_apply
    (hU : ∀ Y ∈ U, ∀ t : Labels, X₀ ∈ D t ↔ Y ∈ D t) (z : U × Rays(X₀)) :
    pathDecoratedFamilyTrivialization T ℳ i₀ x v ν ε c P W S C s hU z =
      ⟨z.1, pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s
        (hU z.1 z.1.property) z.2⟩ := (rfl)

/-- The inverse chart map returns a ray to the reference fiber. -/
@[simp]
theorem pathDecoratedFamilyTrivialization_symm_apply
    (hU : ∀ Y ∈ U, ∀ t : Labels, X₀ ∈ D t ↔ Y ∈ D t)
    (z : Σ Y : U, Rays(Y.val)) :
    (pathDecoratedFamilyTrivialization T ℳ i₀ x v ν ε c P W S C s hU).symm z =
      (z.1, (pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s
        (hU z.1 z.1.property)).symm z.2) := (rfl)

/-- Changing the reference fiber gives a constant transition on an overlap. -/
theorem pathDecoratedFamilyTrivialization_change_base
    (hU : ∀ Y ∈ U, ∀ t : Labels, X₀ ∈ D t ↔ Y ∈ D t) {X₁ : V}
    (h₁ : ∀ Y ∈ U, ∀ t : Labels, X₁ ∈ D t ↔ Y ∈ D t)
    (h₀₁ : ∀ t : Labels, X₀ ∈ D t ↔ X₁ ∈ D t)
    (Y : U) (r : Rays(X₀)) :
    pathDecoratedFamilyTrivialization T ℳ i₀ x v ν ε c P W S C s h₁
        (Y, pathDecoratedRaysEndpointEquiv T ℳ i₀ x v ν ε c P W S C s h₀₁ r) =
      pathDecoratedFamilyTrivialization T ℳ i₀ x v ν ε c P W S C s hU (Y, r) := by
  rw [pathDecoratedFamilyTrivialization_apply, pathDecoratedFamilyTrivialization_apply]
  congr 1
  apply pathDecoratedRays_ext
  simp only [pathDecoratedRaysEndpointEquiv_type]

/-- Each branch of the product chart varies continuously in compact-open path space,
including its entire incoming half-line. -/
theorem continuous_pathDecoratedFamilyTrivialization
    (hU : ∀ Y ∈ U, ∀ t : Labels, X₀ ∈ D t ↔ Y ∈ D t) (r : Rays(X₀)) :
    Continuous fun Y : U =>
      (pathDecoratedFamilyTrivialization T ℳ i₀ x v ν ε c P W S C s hU (Y, r)).2.2.2.ray
        |>.toContinuousMap := by
  exact PathDecoratedRay.continuous_of_history_eq T ℳ i₀ x v ν ε c P W S C
    (fun Y : U => (PathDecoratedRay.endpointEquiv T ℳ i₀ x v ν ε c P W S C r.1.val
      (fun d hd => hU Y Y.property ⟨r.1, ⟨d, hd⟩⟩) r.2)) r.2.1.val continuous_subtype_val
    fun Y => congrArg Subtype.val
      (PathDecoratedRay.endpointEquiv_history T ℳ i₀ x v ν ε c P W S C r.1.val _ r.2)

end Trivialization

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q d => i (w q d)
local notation "Labels'" => PathDecoratedType T ℳ i₀ x s vel ν ε
local notation "D'" => fun t : Labels' => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t)))
  (Path.Degrees.reverseVertexLabels vel i₀ (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C
local notation "Rays'(" X ")" => Σ p : (s : Type _),
  PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C (Subtype.val p) X

include hν hP hW hS hC in
/-- Off one finite arrangement containing every complete type-domain frontier, all actual
rays of the inventory continue over a common convex open neighborhood. There is exactly
one family of fiber bijections preserving complete types, and its paths vary continuously
in compact-open topology. -/
theorem exists_pathDecoratedRay_continuousContinuation :
    ∃ E : ExceptionalArrangement V,
      (∀ t : Labels', frontier (D' t) ⊆ {X | ¬ E.IsGeneric X}) ∧
      ∀ X, E.IsGeneric X → ∃ U : Set V,
        IsOpen U ∧ Convex ℝ U ∧ X ∈ U ∧
        ∃! e : ∀ Y : U, Rays'(X) ≃ Rays'(Y.val),
          (∀ Y r, (⟨(e Y r).1, (e Y r).2.1⟩ : Labels') = ⟨r.1, r.2.1⟩) ∧
          ∀ r, Continuous (fun Y : U => (e Y r).2.2.ray.toContinuousMap) := by
  obtain ⟨E, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement
    (fun t : Labels' => isRationalSemilinear_pathDecoratedDomain
      i₀ ν c P W S C h w hν hP hW hS hC t.1.val t.2.val)
  refine ⟨E, hfrontier, fun X hX => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hstable X hX)
  have hU : ∀ Y ∈ Metric.ball X δ, ∀ t : Labels', X ∈ D' t ↔ Y ∈ D' t :=
    fun Y hY t => (hball Y hY t).symm
  refine ⟨Metric.ball X δ, Metric.isOpen_ball, convex_ball X δ, Metric.mem_ball_self hδ,
    fun Y => pathDecoratedRaysEndpointEquiv T ℳ i₀ x vel ν ε c P W S C s (hU Y Y.property),
    ⟨fun Y r => pathDecoratedRaysEndpointEquiv_type T ℳ i₀ x vel ν ε c P W S C s _ r,
      fun r => continuous_pathDecoratedFamilyTrivialization T ℳ i₀ x vel ν ε c P W S C s hU r⟩,
    fun e he => funext fun Y => eq_pathDecoratedRaysEndpointEquiv T ℳ i₀ x vel ν ε c P W S C s
      (hU Y Y.property) (e Y) (he.1 Y)⟩

end Rational

end Mei
