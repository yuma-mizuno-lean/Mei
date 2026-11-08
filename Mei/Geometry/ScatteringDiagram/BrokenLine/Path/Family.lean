/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Charts
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Evaluation

/-!
# Closed ray charts for finite varying-chamber itineraries

A finite inventory of encounter paths between two chambers gives a finite
semilinear family of all surviving decorated rays. Intermediate chamber modules
and their degree types may differ. Its labels retain the whole encounter path
and complete component history; coincident spatial paths remain distinct.
Its fibers are exactly the actual admissible rays, and the shared weighted
evaluation sums their entire terminal decorations in the final chamber.

Each valid endpoint domain is subdivided into disjoint relative interiors of
closed polyhedra. The closed endpoint and continuous whole-path maps are proper,
and their boundary paths retain incoming-source admission. Properness of each
individual incoming half-line requires a nonzero incoming direction. Boundary
paths are not asserted admissible. This constructs charts for a supplied finite
inventory; geometric encounter bounds and exhaustion of all itineraries are
separate requirements.

For transfer paths use `GradedCorrespondence.totalTransfer` as arrow maps;
inadmissible component steps vanish. The construction reuses
`Quiver.Path.historySupport` and `FiniteSemilinearFamily.ofDomains`, following
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, §3 (arXiv:1601.07081v4), and Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀) (s : Finset (Path a b))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)

/-- Complete path and degree-history labels for a finite encounter inventory. -/
abbrev PathDecoratedType :=
  Σ p : (s : Type _), (pathDecoratedHistorySupport T ℳ i₀ x v ν ε p.val : Type _)

variable (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "Types" => PathDecoratedType T ℳ i₀ x s v ν ε
local notation "Rays" X:max => Σ p : (s : Type _),
  PathDecoratedRay T ℳ i₀ x v ν ε c P W S C (Subtype.val p) X

/-- The sum over actual rays of every itinerary in the supplied inventory. -/
def pathDecoratedEvaluation (X : V) : M b :=
  let := Fintype.ofFinite (Rays X)
  ∑ r : Rays X, r.2.decoration

/-- Evaluate by the entire final decorations of the actual finite ray fibers. -/
theorem pathDecoratedEvaluation_def (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X =
      let := Fintype.ofFinite (Rays X)
      ∑ r : Rays X, r.2.decoration := (rfl)

/-- No actual decorated rays contribute when the incoming coefficient is zero. -/
@[simp]
theorem pathDecoratedEvaluation_zero (X : V) :
    pathDecoratedEvaluation T ℳ i₀ 0 s v ν ε c P W S C X = 0 := by
  simp [pathDecoratedEvaluation_def]

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q d => i (w q d)
local notation "Labels" => PathDecoratedType T ℳ i₀ x s vel ν ε
local notation "dirs" => (fun t : Labels => Path.Degrees.reverseVertexLabels vel i₀
  (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
local notation "D" => (fun t : Labels => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C)
local notation "path" => (fun t : Labels => backwardPath
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t))

include hν hP hW hS hC

/-- All complete varying-chamber types have semilinear full endpoint domains. -/
theorem isRationalSemilinear_pathDecoratedDomain (t : Labels) :
    IsRationalSemilinear h (D t) := by
  simpa only [Path.Degrees.reverseVertexLabels_comp, Function.comp_def] using
    isRationalSemilinear_admissibleBackwardDomain (t.1.val.reverseArrowLabels ν)
      (t.1.val.reverseArrowLabels c) (t.1.val.reverseArrowLabels P) W S C
      (Path.Degrees.reverseVertexLabels w i₀ t.1.val t.2.val)
      (t.1.val.reverseArrowLabels_forall ν
        (fun l => Toric.IsRationalFunctional h l.toLinearMap) hν)
      (t.1.val.reverseArrowLabels_forall P (IsRationalSemilinear h) hP) hW hS hC

/-- The common inclusion family for every surviving history of the finite path
inventory, using its complete geometric admission domain. -/
def pathDecoratedFamily : FiniteSemilinearFamily h h Labels :=
  FiniteSemilinearFamily.ofDomains (fun t => D t)
    (isRationalSemilinear_pathDecoratedDomain T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC)

local notation "F" => pathDecoratedFamily T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC

/-- The chart domain retains all wall, singular and incoming-source constraints. -/
@[simp]
theorem pathDecoratedFamily_domain (t : Labels) : (F).domain t = D t :=
  FiniteSemilinearFamily.ofDomains_domain ..

/-- Evaluation is inclusion of the actual endpoint. -/
@[simp]
theorem pathDecoratedFamily_eval (t : Labels) (X : (F).domain t) :
    (F).eval t X = X.val := FiniteSemilinearFamily.ofDomains_eval ..

/-- Every chart is a finite branch, with no genericity restriction on endpoints. -/
theorem pathDecoratedFamily_isFiniteBranch : (F).IsFiniteBranch :=
  FiniteSemilinearFamily.isFiniteBranch_ofDomains ..

/-- The family fiber is exactly the disjoint union of actual decorated ray
fibers, with the full path and component history as its label. -/
def pathDecoratedFamilyFiberEquiv (X : V) : (F).fiber X ≃
    (Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p.val X) :=
  ((FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ X).trans
    (admissibleRayFiberEquiv W S X (fun t : Labels => t.1.val.length)
      (fun t => t.1.val.reverseArrowLabels ν) (fun t => t.1.val.reverseArrowLabels c)
      (fun t => dirs t) (fun t => t.1.val.reverseArrowLabels P) (fun _ => C)).symm).trans
    (Equiv.sigmaAssoc fun (p : (s : Type _))
      (d : (pathDecoratedHistorySupport T ℳ i₀ x vel ν ε p.val : Type _)) =>
      AdmissibleRayRealization (p.val.reverseArrowLabels ν)
      (p.val.reverseArrowLabels c)
      (Path.Degrees.reverseVertexLabels vel i₀ p.val d.val)
      (p.val.reverseArrowLabels P) W S C X)

local notation "e" X:max =>
  pathDecoratedFamilyFiberEquiv T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC X

/-- The fiber comparison retains the entire encounter path and degree history. -/
@[simp]
theorem pathDecoratedFamilyFiberEquiv_type (X : V) (z : (F).fiber X) :
    (⟨((e X) z).1, ((e X) z).2.1⟩ : Labels) = z.1 := by
  let z' := FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ X z
  have he := congrArg Sigma.fst (admissibleRayFiberEquiv_symm_apply W S X
    (fun t : Labels => t.1.val.length) (fun t => t.1.val.reverseArrowLabels ν)
    (fun t => t.1.val.reverseArrowLabels c) (fun t => dirs t)
    (fun t => t.1.val.reverseArrowLabels P) (fun _ => C) z')
  exact he.trans (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ X z)

/-- Closed-path extension agrees with the full actual ray, including its tail. -/
theorem pathDecoratedFamilyFiberEquiv_path (X : V) (z : (F).fiber X) :
    ((e X) z).2.2.ray.toContinuousMap = (path z.1) X := by
  exact ((e X) z).2.path_eq.trans (congrArg (fun t : Labels => (path t) X)
    (pathDecoratedFamilyFiberEquiv_type T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC X z))

instance (X : V) : Finite ((F).fiber X) :=
  Finite.of_equiv
    (Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p.val X) (e X).symm

/-- Shared weighted evaluation is the sum over actual rays in their final
chamber module, retaining multiplicities even for coincident spatial paths. -/
theorem pathDecoratedFamily_weightedEvaluation (X : V) :
    (F).weightedEvaluation (fun t => t.1.val.homogeneousHistory T ℳ t.2.val x) X =
      pathDecoratedEvaluation T ℳ i₀ x s vel ν ε c P W S C X := by
  let := Fintype.ofFinite ((F).fiber X)
  let := Fintype.ofFinite
    (Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p.val X)
  rw [FiniteSemilinearFamily.weightedEvaluation_def, pathDecoratedEvaluation]
  apply Fintype.sum_equiv (e X)
  intro z
  rw [PathDecoratedRay.decoration_def]
  exact (congrArg (fun t : Labels => t.1.val.homogeneousHistory T ℳ t.2.val x)
    (pathDecoratedFamilyFiberEquiv_type T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC X z)).symm

include hν hP hW hS hC in
/-- Finite closed charts exhaust every actual ray in the itinerary inventory.
Closed extensions are proper in endpoint and compact-open path space, retain
incoming-source admission, and add only limits of the original type domain. -/
theorem exists_pathDecoratedFamily_closedCharts :
    ∃ (κ : Labels → Type) (_ : ∀ t, Finite (κ t)) (A : ∀ t, κ t → Set V),
      (∀ t j, (A t j).Nonempty ∧ IsRationalNormalPolyhedron h (A t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A t j)) ∧
        A t j ⊆ closure (D t) ∧ IsProperMap (fun X : A t j => (X : V)) ∧
        IsProperMap (fun X : A t j => (path t) X.val) ∧
        ∀ X ∈ A t j, (path t) X 0 = X ∧
          (∀ᶠ r : ℝ in atBot, (path t) X r ∈ C) ∧
          (i (w a i₀) ≠ 0 → IsProperMap (fun r : Iic (0 : ℝ) => (path t) X r))) ∧
      (∀ t, Pairwise fun j k => Disjoint (intrinsicInterior ℝ (A t j))
        (intrinsicInterior ℝ (A t k))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (A t j) = D t) ∧
      ∃ E : (Σ t, Σ j : κ t, intrinsicInterior ℝ (A t j)) ≃
          (Σ X, Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p.val X),
        (∀ z, (E z).1 = z.2.2.val) ∧
          ∀ z, (⟨(E z).2.1, (E z).2.2.1⟩ : Labels) = z.1 := by
  obtain ⟨κ, hκ, A, hA, hdisj, hcover, E, hendpoint, hlabel⟩ :=
    FiniteSemilinearFamily.exists_ofDomains_polyhedralCharts (fun t : Labels => D t)
      (isRationalSemilinear_pathDecoratedDomain T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC)
  refine ⟨κ, hκ, A, ?_, hdisj, hcover,
    E.trans (Equiv.sigmaCongrRight fun X => e X), hendpoint, ?_⟩
  · intro t j
    obtain ⟨hne, hpoly, hlc, hsub⟩ := hA t j
    refine ⟨hne, hpoly, hlc, hsub, hpoly.isClosed.isProperMap_subtypeVal, ?_, ?_⟩
    · exact (isProperMap_backwardPath_closure_admissibleBackwardDomain
        _ _ _ _ W S C).comp
        (Topology.IsClosedEmbedding.inclusion hsub
          (hpoly.isClosed.preimage continuous_subtype_val)).isProperMap
    · intro X hX
      have hlim := hsub hX
      refine ⟨backwardPath_apply_zero _ _ _ ?_,
        backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain
          _ _ _ _ W S C hC hlim, fun hv => ?_⟩
      · exact backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain _ _ _ _ W S C hlim
      · apply isProperMap_backwardPath_restrict_Iic
        simpa only [Path.Degrees.reverseVertexLabels_last] using hv
  · intro z
    exact (pathDecoratedFamilyFiberEquiv_type T ℳ i₀ x s ν ε c P W S C
      h w hν hP hW hS hC (E z).1 (E z).2).trans (hlabel z)

end Rational

end Mei
