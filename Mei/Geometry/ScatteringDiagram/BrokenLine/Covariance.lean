/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Affine
public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay

/-!
# Affine covariance of decorated ray fibers

An affine coordinate change gives a bijection of the actual decorated ray fibers
for a signed propagation itinerary. It preserves the entire degree history,
all segment decorations and all encounter times, and maps the complete incoming
path. In particular weighted evaluation is unchanged. Coefficients may be arbitrary
semimodules and the endpoint need not be generic.

We combine `Convex.admissibleRayAffineEquiv` with the whole-component histories
of `DecoratedAdmissibleRay`. The coordinate and decoration conventions follow
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2), and Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V V' J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {n : ℕ} (T : Fin n → Module.End R M) (p₀ : Γ) (a : ℳ p₀)
  (v : Γ → V) (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (ε : Fin n → SignType)
  (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)
  (e : V ≃ᴬ[ℝ] V') (Q : V)

local notation "g" => fun j =>
  ContinuousLinearMap.comp (f j) e.symm.toContinuousAffineMap.contLinear
local notation "b" => fun j => c j - f j (e.symm 0)
local notation "u" => fun p => e.toAffineEquiv.linear (v p)
local notation "Source" => DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q
local notation "Target" => DecoratedAdmissibleRay ℳ T p₀ a u g b ε
  (fun j => e '' P j) (fun j => e '' W j)
  (fun j => e '' S j) (e '' C) (e Q)

/-- Coordinate changes preserve normal velocities and crossing signs, hence
identify exactly the same surviving whole-component histories. -/
@[simp]
theorem decoratedHistorySupport_affine :
    decoratedHistorySupport ℳ T p₀ a u g ε = decoratedHistorySupport ℳ T p₀ a v f ε := by
  classical
  ext p
  simp only [mem_decoratedHistorySupport, ContinuousLinearMap.comp_apply,
    ContinuousAffineMap.coe_contLinear,
    ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
    AffineEquiv.linear_toAffineMap, ContinuousAffineEquiv.toAffineEquiv_symm,
    AffineEquiv.linear_symm, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- Affine changes of coordinates preserve the complete decorated evaluation
fiber, with every encounter retained even when it introduces no geometric bend. -/
def decoratedRayAffineEquiv : Source ≃ Target :=
  Equiv.sigmaCongr
    (Equiv.subtypeEquivRight fun p => by rw [decoratedHistorySupport_affine])
    (fun p => admissibleRayAffineEquiv f c
      (fun j => v (Fin.snoc (α := fun _ => Γ) p.val p₀ j)) P W S C e Q)

/-- The entire recorded degree history is unchanged by the affine comparison. -/
@[simp]
theorem decoratedRayAffineEquiv_history (r : Source) :
    (decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q r).1.val = r.1.val := (rfl)

/-- Every segment keeps its whole homogeneous decoration. -/
@[simp]
theorem decoratedRayAffineEquiv_decoration (r : Source) (j : Fin (n + 1)) :
    (decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q r).decoration j =
      r.decoration j := by
  simp only [DecoratedAdmissibleRay.decoration_def, decoratedRayAffineEquiv_history]

/-- The realized path, including its incoming tail, transforms affinely. -/
@[simp]
theorem decoratedRayAffineEquiv_ray (r : Source) :
    (decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q r).2.ray =
      r.2.ray.map e.toAffineEquiv.toAffineMap :=
  admissibleRayAffineEquiv_ray f c _ P W S C e Q r.2

/-- Coordinate changes preserve the full encounter-parameter list. -/
@[simp]
theorem decoratedRayAffineEquiv_parameter (r : Source) :
    (decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q r).2.parameter =
      r.2.parameter :=
  admissibleRayAffineEquiv_parameter f c _ P W S C e Q r.2

/-- The inverse comparison retains the entire recorded degree history. -/
@[simp]
theorem decoratedRayAffineEquiv_symm_history (r : Target) :
    ((decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q).symm r).1.val = r.1.val := (rfl)

/-- The inverse comparison maps the whole path by the inverse affine map. -/
@[simp]
theorem decoratedRayAffineEquiv_symm_ray (r : Target) :
    ((decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q).symm r).2.ray =
      r.2.ray.map e.symm.toAffineEquiv.toAffineMap :=
  admissibleRayAffineEquiv_symm_ray f c _ P W S C e Q r.2

/-- The inverse comparison preserves all encounter times. -/
@[simp]
theorem decoratedRayAffineEquiv_symm_parameter (r : Target) :
    ((decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q).symm r).2.parameter =
      r.2.parameter :=
  admissibleRayAffineEquiv_symm_parameter f c _ P W S C e Q r.2

/-- Affine covariance of the finite weighted evaluation, without any endpoint
or geometric finiteness hypothesis. Only contributing histories are summed. -/
@[simp]
theorem decoratedRayEvaluation_affine :
    decoratedRayEvaluation ℳ T p₀ a u g b ε
      (fun j => e '' P j) (fun j => e '' W j)
      (fun j => e '' S j) (e '' C) (e Q) =
        decoratedRayEvaluation ℳ T p₀ a v f c ε P W S C Q := by
  classical
  let := Fintype.ofFinite Source
  let := Fintype.ofFinite Target
  simp only [decoratedRayEvaluation_def]
  exact (Fintype.sum_equiv (decoratedRayAffineEquiv ℳ T p₀ a v f c ε P W S C e Q)
    _ _ (fun r => (decoratedRayAffineEquiv_decoration ℳ T p₀ a v f c ε P W S C e Q r 0).symm)).symm

end Mei
