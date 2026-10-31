/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Charts
public import Mei.Geometry.Convex.Sweep.Admissible.Limit
public import Mei.Geometry.Convex.Sweep.LimitRay

/-!
# Closed charts for the full decorated ray family

Every cutoff decorated type has a continuous extension of its geometric paths
from its valid endpoint domain to its closure. At a boundary endpoint the
extension is a finite affine ray on the negative half-line: encounters may
collapse, while selected closed-support incidences and the incoming polyhedral
source persist. The decoration and the entire degree and encounter history stay
attached to the type, even when geometric bends cancel.

The full cutoff family admits finitely many closed polyhedral endpoint charts
with proper endpoint and compact-open path maps. Their interiors partition each
valid type domain. This supplies degeneration charts, without asserting that
boundary paths are admissible or classifying their boundary events.

We combine `exists_cutoffDecoratedRay_polyhedralCharts`,
`closure_admissibleBackwardDomain_subset_weakBackwardDomain`, and
`backwardLimitRay`. The endpoint parameterization follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P W : J → Set V) (S : K → Set V) (C : Set V)

namespace CutoffDecoratedType

variable (t : CutoffDecoratedType d ℳ T a v f ε k)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "A" => fun j => P (t.itinerary.val.get j)
local notation "D" => domain c P W S C t

/-- The continuous hinge extension of a type's paths to all endpoints.
On the closure of its valid domain it retains the endpoint and weak time order. -/
def path : C(V, C(ℝ, V)) := backwardPath F b u

/-- The path extension is the backward hinge family of the recorded itinerary. -/
theorem path_def : t.path c = backwardPath F b u := (rfl)

/-- Limiting endpoints retain nonnegative elapsed times, including at terminal
and multiple-encounter collapses. -/
theorem backwardTime_nonneg {Q : V} (hQ : Q ∈ closure D)
    (j : Fin t.itinerary.val.length) :
    0 ≤ backwardTime F b (fun j => u j.castSucc) j Q :=
  backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain F b u A W S C
    (by simpa only [domain_def] using hQ) j

/-- With nonnegative elapsed times, the path extension retains its endpoint. -/
theorem path_apply_zero {Q : V}
    (hQ : ∀ j, 0 ≤ backwardTime F b (fun j => u j.castSucc) j Q) :
    t.path c Q 0 = Q := by
  rw [path_def]
  exact backwardPath_apply_zero F b u hQ

/-- Every recorded encounter remains on its selected closed support, even when
its time coincides with another encounter or with the endpoint. -/
theorem path_parameter_mem (hP : ∀ j, IsClosed (P j)) {Q : V} (hQ : Q ∈ closure D)
    (j : Fin t.itinerary.val.length) :
    t.path c Q (backwardParameter F b (fun j => u j.castSucc) j.succ Q) ∈ A j := by
  rw [path_def, backwardPath_apply_parameter F b u (t.backwardTime_nonneg c P W S C hQ)]
  have hw := closure_admissibleBackwardDomain_subset_weakBackwardDomain F b u A W S C
    (fun j => hP (t.itinerary.val.get j)) (by simpa only [domain_def] using hQ)
  exact ((mem_weakBackwardDomain F b _ A Q).mp hw j).2

/-- The extension over a type's closed endpoint domain is proper in compact-open
path space. This does not require nonzero incoming velocity. -/
theorem isProperMap_path_closure :
    IsProperMap (fun Q : closure D => t.path c Q.val) := by
  rw [path_def]
  exact isProperMap_backwardPath_restrict F b u isClosed_closure
    (fun _ hQ => t.backwardTime_nonneg c P W S C hQ)

/-- Every compact-open limit of paths of a fixed type comes from a limiting
endpoint, and every limiting endpoint gives such a limit. -/
theorem closure_image_path : closure (t.path c '' D) = t.path c '' closure D := by
  simpa only [path_def, domain_def] using
    closure_image_backwardPath_admissibleBackwardDomain F b u A W S C

/-- Each boundary path is an actual finite affine ray on the negative half-line.
Its incoming direction is unchanged; canceled bends do not delete type records. -/
theorem exists_limitRay {Q : V} (hQ : Q ∈ closure D) :
    ∃ β : FiniteAffineRay V V, β.endpoint = Q ∧ β.incomingDirection = v 0 ∧
      ∀ s : ℝ, s ≤ 0 → β s = t.path c Q s := by
  let h0 := t.backwardTime_nonneg c P W S C hQ
  refine ⟨backwardLimitRay F b u Q h0, endpoint_backwardLimitRay F b u Q h0, ?_, ?_⟩
  · simp only [incomingDirection_backwardLimitRay, Fin.snoc_last]
  · intro s hs
    rw [backwardLimitRay_apply F b u Q h0 hs, path_def]

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i}

/-- A polyhedral incoming source persists throughout the closed type domain.
The entry time may depend on the endpoint. -/
theorem path_eventually_mem (hC : IsRationalNormalPolyhedron h C)
    {Q : V} (hQ : Q ∈ closure D) : ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C := by
  rw [path_def]
  exact backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain F b u A W S C hC
    (by simpa only [domain_def] using hQ)

end CutoffDecoratedType

/-- The path of an actual cutoff ray is the extension of its exact decorated
type at its endpoint. -/
theorem CutoffDecoratedRay.toContinuousMap_eq_typePath [Finite J] {Q : V}
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.realization.2.ray.toContinuousMap =
      (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val.path c Q := by
  rw [cutoffDecoratedRayFiberEquiv_apply_val, CutoffDecoratedType.path_def,
    AdmissibleRayRealization.toContinuousMap_eq_backwardPath]

/-- All compact-open limits of the full cutoff ray family are accounted for by
closing the endpoint domains of its finite decorated types. A limit may pass
through singular sets or have collapsed encounters. Distinct types remain indexed
separately even when their paths coincide. -/
theorem closure_range_cutoffDecoratedRay [Finite J] :
    closure (range (fun z : Σ Q, CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q =>
      z.2.realization.2.ray.toContinuousMap)) =
      ⋃ t : CutoffDecoratedType d ℳ T a v f ε k,
        t.path c '' closure (CutoffDecoratedType.domain c P W S C t) := by
  have hrange : range (fun z : Σ Q, CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q =>
      z.2.realization.2.ray.toContinuousMap) =
      ⋃ t : CutoffDecoratedType d ℳ T a v f ε k,
        t.path c '' CutoffDecoratedType.domain c P W S C t := by
    ext γ
    constructor
    · rintro ⟨⟨Q, r⟩, rfl⟩
      let z := cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r
      exact mem_iUnion.mpr ⟨z.val, Q, z.property,
        (r.toContinuousMap_eq_typePath c P W S C).symm⟩
    · intro hγ
      obtain ⟨t, Q, hQ, rfl⟩ := mem_iUnion.mp hγ
      let r := (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q).symm ⟨t, hQ⟩
      refine ⟨⟨Q, r⟩, ?_⟩
      simpa only [r, Equiv.apply_symm_apply] using r.toContinuousMap_eq_typePath c P W S C
  rw [hrange, closure_iUnion_of_finite]
  simp_rw [CutoffDecoratedType.closure_image_path]

section Rational

variable (d ℳ T a f ε) [Finite J] [Finite K]
  {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ)
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j)) (hclosed : ∀ j, IsClosed (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

include hf hP hclosed hW hS hC

/-- The entire cutoff family has finite closed degeneration charts, retaining
selected supports and the incoming source on every boundary path. The endpoint
and compact-open path maps are proper. Interior charts recover exactly the valid
type domains, with their original histories and decorations. This does not assert
boundary admissibility or a classification of boundary events. -/
theorem exists_cutoffDecoratedRay_closedCharts (k : ℕ) :
    ∃ (ι : CutoffDecoratedType d ℳ T a (fun q => i (w q)) f ε k → Type)
      (_ : ∀ t, Finite (ι t)) (B : ∀ t, ι t → Set V),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧
        B t j ⊆ closure (CutoffDecoratedType.domain c P W S C t) ∧
        IsProperMap (fun Q : B t j => (Q : V)) ∧
        IsProperMap (fun Q : B t j => t.path c Q.val) ∧
        ∀ Q ∈ B t j,
          (∀ e : Fin t.itinerary.val.length,
            t.path c Q (backwardParameter (fun e => f (t.itinerary.val.get e))
              (fun e => c (t.itinerary.val.get e))
              (fun e => i (w (t.history.val e))) e.succ Q) ∈ P (t.itinerary.val.get e)) ∧
          (∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C) ∧
          ∃ β : FiniteAffineRay V V, β.endpoint = Q ∧ β.incomingDirection = i (w 0) ∧
            ∀ s : ℝ, s ≤ 0 → β s = t.path c Q s) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      ∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = CutoffDecoratedType.domain c P W S C t := by
  obtain ⟨ι, hι, B, hB, hdisj, hcover, _⟩ :=
    exists_cutoffDecoratedRay_polyhedralCharts d ℳ T a f c ε P W S C h w hf
      hP hW hS hC k
  refine ⟨ι, hι, B, ?_, hdisj, hcover⟩
  intro t j
  obtain ⟨hne, hpoly, hlc, hsub⟩ := hB t j
  refine ⟨hne, hpoly, hlc, hsub, hpoly.isClosed.isProperMap_subtypeVal, ?_, ?_⟩
  · rw [CutoffDecoratedType.path_def]
    exact isProperMap_backwardPath_restrict _ _ _ hpoly.isClosed
      (fun Q hQ => t.backwardTime_nonneg c P W S C (hsub hQ))
  · intro Q hQ
    refine ⟨?_, t.path_eventually_mem c P W S C hC (hsub hQ),
      t.exists_limitRay c P W S C (hsub hQ)⟩
    intro e
    simpa only [Fin.snoc_castSucc] using
      t.path_parameter_mem c P W S C hclosed (hsub hQ) e

end Rational

end Mei
