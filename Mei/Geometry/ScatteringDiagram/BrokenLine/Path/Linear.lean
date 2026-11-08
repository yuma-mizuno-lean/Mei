/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Uniform
public import Mei.LinearAlgebra.FiniteInput
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Linear evaluation of rays through varying chambers

For a finite encounter inventory, the weighted sum of actual decorated rays is
linear on the entire incoming homogeneous module. Neither the chamber modules
nor their grading supports need be finite. Individual fibers may change under
addition or scalar multiplication: components can cancel or be killed.

The existing uniform history expansion on each finite span supplies the finite
input tests of `Function.existsUnique_linearMap_of_finite_span_interpolation`.
The resulting operator therefore evaluates the actual fibers, retaining all
crossing, wall-avoidance, singular and global incoming-source conditions.
Its restriction to a uniformly supported incoming family is the existing finite
sum of geometric component maps. Such restrictions, rather than finiteness of
the whole incoming module, suffice for local resolution identities.

Whole-component propagation follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
The closed-chart interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (s : Finset (Path a b))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

private theorem existsUnique_pathDecoratedEvaluation_linearMap (X : V) :
    ∃! L : ℳ a i₀ →ₗ[R] M b, ∀ x,
      L x = pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X := by
  classical
  apply Function.existsUnique_linearMap_of_finite_span_interpolation
  intro t
  let A := Submodule.span R (t : Set (ℳ a i₀))
  obtain ⟨D, -, heval⟩ := exists_uniform_pathDecoratedEvaluation_expansion
    T ℳ i₀ s v ν ε c P W S C A.subtype (by
      rw [Submodule.range_subtype]
      exact Submodule.fg_span t.finite_toSet)
  let L : A →ₗ[R] M b := ∑ p : (s : Type _), ∑ d ∈ D p,
    if (∀ j, p.val.reverseArrowLabels ν j
          (Path.Degrees.reverseVertexLabels v i₀ p.val d j.castSucc) =
        p.val.reverseArrowLabels ν j
          (Path.Degrees.reverseVertexLabels v i₀ p.val d j.succ) ∧
      SignType.sign (p.val.reverseArrowLabels ν j
          (Path.Degrees.reverseVertexLabels v i₀ p.val d j.castSucc)) =
        p.val.reverseArrowLabels ε j) ∧
      X ∈ admissibleBackwardDomain (p.val.reverseArrowLabels ν)
        (p.val.reverseArrowLabels c) (Path.Degrees.reverseVertexLabels v i₀ p.val d)
        (p.val.reverseArrowLabels P) W S C
    then (p.val.homogeneousHistory T ℳ d).comp ((ℳ a i₀).subtype.comp A.subtype)
    else 0
  refine ⟨L, fun x hx => ?_⟩
  simpa only [Submodule.subtype_apply] using (heval X ⟨x, Submodule.subset_span hx⟩).symm

/-- Weighted evaluation of actual varying-chamber rays as a linear map on the
whole incoming homogeneous piece. No uniform finite support on that piece is
required; finite input tests use their own finite history inventories. -/
def pathDecoratedEvaluationLinearMap (X : V) : ℳ a i₀ →ₗ[R] M b :=
  (existsUnique_pathDecoratedEvaluation_linearMap T ℳ i₀ s v ν ε c P W S C X).choose

/-- The operator evaluates the original actual-ray fibers, including when
addition or scalar multiplication changes their surviving histories. -/
@[simp]
theorem pathDecoratedEvaluationLinearMap_apply (X : V) (x : ℳ a i₀) :
    pathDecoratedEvaluationLinearMap T ℳ i₀ s v ν ε c P W S C X x =
      pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X :=
  (existsUnique_pathDecoratedEvaluation_linearMap T ℳ i₀ s v ν ε c P W S C X).choose_spec.1 x

/-- Whole-component ray evaluations are additive, including cancellation of
entire histories and without any assumption on the endpoint. -/
@[simp]
theorem pathDecoratedEvaluation_add (X : V) (x y : ℳ a i₀) :
    pathDecoratedEvaluation T ℳ i₀ (x + y) s v ν ε c P W S C X =
      pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X +
        pathDecoratedEvaluation T ℳ i₀ y s v ν ε c P W S C X := by
  simpa only [pathDecoratedEvaluationLinearMap_apply] using
    (pathDecoratedEvaluationLinearMap T ℳ i₀ s v ν ε c P W S C X).map_add x y

/-- Scalars commute with actual ray evaluation even when they kill individual
whole decorations. The scalar semiring may be noncommutative. -/
@[simp]
theorem pathDecoratedEvaluation_smul (X : V) (r : R) (x : ℳ a i₀) :
    pathDecoratedEvaluation T ℳ i₀ (r • x) s v ν ε c P W S C X =
      r • pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X := by
  simpa only [pathDecoratedEvaluationLinearMap_apply] using
    (pathDecoratedEvaluationLinearMap T ℳ i₀ s v ν ε c P W S C X).map_smul r x

variable {E : Type*} [AddCommMonoid E] [Module R E] (α : E →ₗ[R] ℳ a i₀)

local notation "input" => LinearMap.comp (Submodule.subtype (ℳ a i₀)) α
local notation "dirs(" p ", " d ")" => Path.Degrees.reverseVertexLabels v i₀ p d
local notation "normals(" p ")" => Path.reverseArrowLabels ν p
local notation "N(" p ", " d ")" => (fun j : Fin (Path.length p) =>
  normals(p) j (dirs(p, d) (Fin.castSucc j)) = normals(p) j (dirs(p, d) (Fin.succ j)) ∧
    SignType.sign (normals(p) j (dirs(p, d) (Fin.castSucc j))) = Path.reverseArrowLabels ε p j)
local notation "D(" p ", " d ")" => admissibleBackwardDomain normals(p)
  (Path.reverseArrowLabels c p) dirs(p, d) (Path.reverseArrowLabels P p) W S C
local notation "H(" p ", " d ")" => LinearMap.comp (Path.homogeneousHistory T ℳ p d) input

open Classical in
/-- On any uniformly supported incoming family, the global evaluation operator
is the finite sum of the component maps selected by their full geometric domains.
This is an identity of linear maps, retaining zero terms for individual inputs. -/
theorem pathDecoratedEvaluationLinearMap_comp_eq_sum
    (A : ∀ p : (s : Type _), Finset (p.val.Degrees ι))
    (hA : ∀ p d, d ∉ A p → H(p.val, d) = 0) (X : V) :
    (pathDecoratedEvaluationLinearMap T ℳ i₀ s v ν ε c P W S C X).comp α =
      ∑ p : (s : Type _), ∑ d ∈ A p,
        if (∀ j, N(p.val, d) j) ∧ X ∈ D(p.val, d) then H(p.val, d) else 0 := by
  ext x
  simpa only [LinearMap.comp_apply, pathDecoratedEvaluationLinearMap_apply] using
    pathDecoratedEvaluation_eq_uniform_sum T ℳ i₀ s v ν ε c P W S C α A hA X x

end Mei
