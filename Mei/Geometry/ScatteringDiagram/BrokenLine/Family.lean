/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Evaluation
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Charts

/-!
# The finite semilinear family of affine decorated rays

The complete cutoff inventory defines a `FiniteSemilinearFamily`, with one
inclusion chart for every complete decorated type. Its endpoint domain is the
existing admissible backward domain, including the incoming-source condition
and avoidance of unrecorded walls and singularities. Its fibers are equivalent
to actual cutoff decorated rays, preserving their entire type and final weight.
Thus the shared family's weighted evaluation recovers the existing affine sum.

Restriction acts on endpoint domains. In particular it retains the original
incoming tails and any bends outside the restricting set. This permits comparing
the same global histories on endpoint covers.

The construction reuses `cutoffDecoratedRayFiberEquiv` and the semilinearity of
its type domains. The endpoint-family interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2); whole-component decorations follow
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 and Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

variable {R M Γ V J K I Λ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (a : ℳ 0) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)
  [AddCommGroup Λ] {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (w : Γ → Λ) [Finite J] [Finite K] [Finite I]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C) (k : ℕ)

local notation "Types" => CutoffDecoratedType d ℳ T a (fun q => i (w q)) f ε k
local notation "Rays" Q => CutoffDecoratedRay d ℳ T a (fun q => i (w q)) f c ε P W S C k Q

/-- The finite semilinear family of all affine cutoff decorated rays, indexed by
their complete types and evaluated by their endpoints. -/
def cutoffBrokenLineFamily : FiniteSemilinearFamily h h Types :=
  FiniteSemilinearFamily.ofDomains (CutoffDecoratedType.domain c P W S C)
    (fun t => t.isRationalSemilinear_domain c P W S C h w hf hP hW hS hC)

local notation "F" => cutoffBrokenLineFamily d ℳ T a f c ε P W S C h w hf hP hW hS hC k

/-- A chart retains the full global admissible endpoint condition of its type. -/
@[simp]
theorem cutoffBrokenLineFamily_domain (t : Types) :
    (F).domain t = CutoffDecoratedType.domain c P W S C t :=
  FiniteSemilinearFamily.ofDomains_domain ..

@[simp]
theorem cutoffBrokenLineFamily_eval (t : Types) (Q : (F).domain t) :
    (F).eval t Q = Q.val := FiniteSemilinearFamily.ofDomains_eval ..

/-- All charts are finite branches. This applies on their complete domains,
including lower-dimensional strata and nongeneric endpoints. -/
theorem cutoffBrokenLineFamily_isFiniteBranch : (F).IsFiniteBranch :=
  FiniteSemilinearFamily.isFiniteBranch_ofDomains ..

/-- Finite closed polyhedral charts parameterize the common family with its
full type labels. Their boundaries add only limits of valid endpoints. -/
theorem exists_cutoffBrokenLineFamily_polyhedralCharts :
    ∃ (κ : Types → Type) (_ : ∀ t, Finite (κ t)) (B : ∀ t, κ t → Set V),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧
        B t j ⊆ closure (CutoffDecoratedType.domain c P W S C t)) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = CutoffDecoratedType.domain c P W S C t) ∧
      ∃ e : (Σ t, Σ j : κ t, intrinsicInterior ℝ (B t j)) ≃ (Σ Q, (F).fiber Q),
        (∀ z, (e z).1 = z.2.2.val) ∧ ∀ z, (e z).2.1 = z.1 :=
  FiniteSemilinearFamily.exists_ofDomains_polyhedralCharts _ _

/-- The fiber of the shared semilinear family is exactly the actual decorated
ray fiber, with no quotient of coincident types or restriction to generic points. -/
def cutoffBrokenLineFamilyFiberEquiv (Q : V) : (F).fiber Q ≃ Rays Q :=
  (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q).trans
    (cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q)) f c ε P W S C k Q).symm

local notation "e" Q =>
  cutoffBrokenLineFamilyFiberEquiv d ℳ T a f c ε P W S C h w hf hP hW hS hC k Q

/-- Reconstructing the ray preserves its entire decorated type, including all
encounters and the whole component history. -/
@[simp↓] -- Read the type before the original equivalence expands its structure fields.
theorem cutoffBrokenLineFamilyFiberEquiv_type (Q : V) (z : (F).fiber Q) :
    (cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q)) f c ε P W S C k Q
      ((e Q) z)).val = z.1 := by
  have ht := (cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q))
    f c ε P W S C k Q).apply_symm_apply
      (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q z)
  exact (congrArg Subtype.val ht).trans
    (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ Q z)

/-- The inverse comparison assigns an actual ray its original complete type. -/
@[simp]
theorem cutoffBrokenLineFamilyFiberEquiv_symm_type (Q : V) (r : Rays Q) :
    ((e Q).symm r).1 =
      (cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q)) f c ε P W S C k Q r).val := by
  have ht := cutoffBrokenLineFamilyFiberEquiv_type d ℳ T a f c ε P W S C
    h w hf hP hW hS hC k Q ((e Q).symm r)
  simpa only [Equiv.apply_symm_apply] using ht.symm

/-- Chart weights are the final whole decorations of the reconstructed rays. -/
@[simp↓]
theorem cutoffBrokenLineFamilyFiberEquiv_decoration (Q : V) (z : (F).fiber Q) :
    ((e Q) z).decoration = z.1.decoration := by
  rw [← cutoffDecoratedRayFiberEquiv_decoration d ℳ T a (fun q => i (w q))
    f c ε P W S C k Q, cutoffBrokenLineFamilyFiberEquiv_type]

/-- The common family has finite endpoint fibers via its actual ray equivalence. -/
instance (Q : V) : Finite ((F).fiber Q) :=
  Finite.of_equiv (Rays Q) (e Q).symm

/-- Weighted evaluation in the common family recovers the original sum over
all affine rays, including unchanged-degree and simultaneous encounters. -/
theorem cutoffBrokenLineFamily_weightedEvaluation (Q : V) :
    (F).weightedEvaluation CutoffDecoratedType.decoration Q =
      cutoffDecoratedEvaluation d ℳ T a (fun q => i (w q)) f c ε P W S C k Q := by
  let := Fintype.ofFinite ((F).fiber Q)
  let := Fintype.ofFinite (Rays Q)
  rw [FiniteSemilinearFamily.weightedEvaluation_def, cutoffDecoratedEvaluation_def]
  exact Fintype.sum_equiv (e Q) _ _ fun z =>
    (cutoffBrokenLineFamilyFiberEquiv_decoration d ℳ T a f c ε P W S C
      h w hf hP hW hS hC k Q z).symm

variable {U : Set V} (hU : IsRationalSemilinear h U)

open Classical in
/-- Endpoint restriction leaves the affine evaluation unchanged inside the set
and gives zero outside. No local replacement of the incoming source is made. -/
theorem cutoffBrokenLineFamily_restrict_weightedEvaluation (Q : V) :
    ((F).restrict hU).weightedEvaluation CutoffDecoratedType.decoration Q =
      if Q ∈ U then
        cutoffDecoratedEvaluation d ℳ T a (fun q => i (w q)) f c ε P W S C k Q else 0 := by
  calc
    ((F).restrict hU).weightedEvaluation CutoffDecoratedType.decoration Q =
        if Q ∈ U then (F).weightedEvaluation CutoffDecoratedType.decoration Q else 0 :=
      FiniteSemilinearFamily.weightedEvaluation_ofDomains_restrict hU _ Q
    _ = _ := by rw [cutoffBrokenLineFamily_weightedEvaluation]

end Mei
