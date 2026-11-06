/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Transfer
public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace.Limit
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Charts
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Evaluation

/-!
# Closed families of single-face transfer rays

The nonzero whole transfers of a homogeneous input index a finite semilinear
endpoint family. Its fibers are the actual single-face rays between possibly
different chamber modules, and its weighted evaluation is their existing sum.
Distinct output degrees retain their multiplicities even when their paths agree.

Each endpoint domain has disjoint polyhedral interior charts with proper closed
extensions in compact-open path space. The extensions retain the full incoming
half-line. Every excluded limiting endpoint is terminal or has a singular crossing.
This necessary classification allows any semilinear singular subset of the face.
Boundary paths are retained as degenerations, without asserting admissibility.

We use the shared inclusion-family charts, admissible backward realizations and
their continuous hinge extensions. The endpoint-family interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2); whole-component propagation through a face follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei.GradedCorrespondence

variable {R B U M ι κ V Λ : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid M] [Module R M] [DecidableEq κ]
  {𝒰 : ι → Submodule R U} {ℳ : κ → Submodule R M}
  [DirectSum.Decomposition ℳ] {I : Set ι} {J : Set κ}
  (C : GradedCorrespondence (B := B) 𝒰 ℳ I J) (p : I) (a : 𝒰 p)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup Λ] {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (w₀ : Λ) (w : κ → Λ) (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)
  (hν : Toric.IsRationalFunctional h ν.toLinearMap)
  (hZ : Z ⊆ {x | ν x = b}) (hsemi : IsRationalSemilinear h Z)

local notation "u" => i w₀
local notation "v" => fun q => i (w q)
local notation "D" q:max => admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b)
  ![i (w q), u] (fun _ => Set.ofPred fun x => ν x = b) (fun _ : Unit => Set.ofPred fun x => ν x = b)
  (fun _ : Unit => Z) (Set.ofPred fun x => 0 < (ν x - b) / ν u)
local notation "path" q:max => backwardPath (fun _ : Fin 1 => ν) (fun _ => b) ![i (w q), u]
local notation "labels" => (Finset.filter (fun q => ν (i (w q)) = ν u)
  (DFinsupp.support (DirectSum.decompose ℳ (C.right (C.liftLeft p a)))) : Type _)
local notation "Rays" Q => C.SingleFaceTransferRay p a u v ν b Z Q

open Classical in
/-- The shared endpoint family of actual one-crossing transfer rays. Each label
records one nonzero entire output component with the conserved normal velocity. -/
def singleFaceTransferFamily : FiniteSemilinearFamily h h labels :=
  FiniteSemilinearFamily.ofDomains (fun q => D q.val) (fun q => by
    have hn := (Finset.mem_filter.mp q.property).2
    have ht := (IsRationalSemilinear.setOf_nonpos
      (isRationalFunctional_backwardTime (fun _ : Fin 1 => ν) (fun _ => b)
        (fun _ => w q.val) (fun _ => hν) 0)).compl
    have hx := hsemi.compl.preimage _ (isRationalLinearMap_sweepProjection hν b (w q.val))
    convert ht.inter hx using 1
    ext Q
    simp only [mem_admissibleBackwardDomain_singleFace_one_iff hn hZ,
      mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_le, backwardTime_apply,
      Fin.castSucc_zero, backwardPoint_zero, ContinuousAffineMap.coe_id, id_eq, mem_preimage]
    exact and_congr_left fun _ => by rw [← neg_sub (ν Q) b, neg_div, neg_pos])

local notation "F" => C.singleFaceTransferFamily p a h w₀ w ν b Z hν hZ hsemi

open Classical in
/-- A branch retains the complete admissible endpoint condition, including its
full incoming source half-space and avoidance of the singular subset. -/
@[simp]
theorem singleFaceTransferFamily_domain (q : labels) : (F).domain q = D q.val :=
  FiniteSemilinearFamily.ofDomains_domain ..

open Classical in
/-- Evaluation is the endpoint inclusion on each admitted branch. -/
@[simp]
theorem singleFaceTransferFamily_eval (q : labels) (Q : (F).domain q) :
    (F).eval q Q = Q.val := FiniteSemilinearFamily.ofDomains_eval ..

open Classical in
/-- Every branch is finite over endpoint space, including nongeneric endpoints. -/
theorem singleFaceTransferFamily_isFiniteBranch : (F).IsFiniteBranch :=
  FiniteSemilinearFamily.isFiniteBranch_ofDomains ..

open Classical in
/-- Inclusion-family fibers reconstruct the original admissible transfer rays.
No coincident paths or distinct degree labels are identified. -/
def singleFaceTransferFamilyFiberEquiv (Q : V) : (F).fiber Q ≃ Rays Q :=
  (FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q).trans
    (admissibleRayFiberEquiv (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z) Q
      (fun _ : labels => 1) (fun _ _ => ν) (fun _ _ => b)
      (fun q => ![i (w q.val), u]) (fun _ _ => {x | ν x = b})
      (fun _ => {x | 0 < (ν x - b) / ν u})).symm

local notation "e" Q => C.singleFaceTransferFamilyFiberEquiv p a h w₀ w ν b Z hν hZ hsemi Q

open Classical in
/-- Reconstruction preserves the entire output-degree label. -/
@[simp]
theorem singleFaceTransferFamilyFiberEquiv_label (Q : V) (z : (F).fiber Q) :
    ((e Q) z).1 = z.1 := by
  let z' := FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q z
  have he := congrArg Sigma.fst (admissibleRayFiberEquiv_symm_apply
    (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z) Q
    (fun _ : labels => 1) (fun _ _ => ν) (fun _ _ => b)
    (fun q => ![i (w q.val), u]) (fun _ _ => {x | ν x = b})
    (fun _ => {x | 0 < (ν x - b) / ν u}) z')
  exact he.trans (FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val _ _ Q z)

open Classical in
/-- The inverse comparison retains the ray's original output-degree label. -/
@[simp]
theorem singleFaceTransferFamilyFiberEquiv_symm_label (Q : V) (r : Rays Q) :
    ((e Q).symm r).1 = r.1 := by
  have he := C.singleFaceTransferFamilyFiberEquiv_label p a h w₀ w ν b Z hν hZ hsemi
    Q ((e Q).symm r)
  simpa only [Equiv.apply_symm_apply] using he.symm

open Classical in
/-- The family path is the whole actual ray, including its individual incoming
tail and its continuation after time zero. -/
@[simp↓]
theorem singleFaceTransferFamilyFiberEquiv_path (Q : V) (z : (F).fiber Q) :
    ((e Q) z).2.ray.toContinuousMap = (path z.1.val) Q := by
  rw [AdmissibleRayRealization.toContinuousMap_eq_backwardPath,
    singleFaceTransferFamilyFiberEquiv_label]

open Classical in
instance (Q : V) : Finite ((F).fiber Q) :=
  (C.singleFaceTransferFamily_isFiniteBranch p a h w₀ w ν b Z hν hZ hsemi).finite_fiber Q

open Classical in
/-- Summing the branch weights in the shared family computes exactly the
existing weighted sum over actual transfer rays, with whole decorations. -/
theorem singleFaceTransferFamily_weightedEvaluation (Q : V) :
    (F).weightedEvaluation (fun q => (C.transfer p q.val a : M)) Q =
      C.singleFaceTransferEvaluation p a u v ν b Z Q := by
  let := Fintype.ofFinite ((F).fiber Q)
  let := Fintype.ofFinite (Rays Q)
  rw [FiniteSemilinearFamily.weightedEvaluation_def, singleFaceTransferEvaluation_def]
  exact Fintype.sum_equiv (e Q) _ _ (fun z => by
    rw [singleFaceTransferFamilyFiberEquiv_label])

include hν hZ hsemi in
open Classical in
/-- Finite closed charts exhaust the actual transfer-ray family. Each chart has
proper endpoint and whole-path maps; all new points are limits of valid rays.
The relative interiors are disjoint separately for each whole output degree. -/
theorem exists_singleFaceTransferFamily_closedCharts :
    ∃ (ι' : labels → Type) (_ : ∀ q, Finite (ι' q)) (A : ∀ q, ι' q → Set V),
      (∀ q j, (A q j).Nonempty ∧ IsRationalNormalPolyhedron h (A q j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A q j)) ∧
        A q j ⊆ closure (D q.val) ∧
        IsProperMap (fun Q : A q j => (Q : V)) ∧
        IsProperMap (fun Q : A q j => (path q.val) Q.val) ∧
        ∀ Q ∈ A q j,
          (∀ᶠ s : ℝ in Filter.atBot,
            (path q.val) Q s ∈ {x | 0 < (ν x - b) / ν u}) ∧
          (path q.val) Q 0 = Q ∧
          IsProperMap (fun s : Iic (0 : ℝ) => (path q.val) Q s) ∧
          (Q ∉ D q.val → ν Q = b ∨
            ((ν Q - b) / ν (i (w q.val)) < 0 ∧
              (path q.val) Q ((ν Q - b) / ν (i (w q.val))) ∈ Z))) ∧
      (∀ q, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (A q j))
        (intrinsicInterior ℝ (A q l))) ∧
      (∀ q, ⋃ j, intrinsicInterior ℝ (A q j) = D q.val) ∧
      ∃ E : (Σ q, Σ j : ι' q, intrinsicInterior ℝ (A q j)) ≃ (Σ Q, Rays Q),
        (∀ z, (E z).1 = z.2.2.val) ∧ ∀ z, (E z).2.1 = z.1 := by
  obtain ⟨ι', hι', A, hA, hdisj, hcover, E, hendpoint, hlabel⟩ :=
    FiniteSemilinearFamily.exists_ofDomains_polyhedralCharts (fun q : labels => D q.val)
      (fun q => by
        simpa only [singleFaceTransferFamily_domain] using
          ((F).isRationalPiecewiseAffine q).isRationalSemilinear)
  refine ⟨ι', hι', A, ?_, hdisj, hcover,
    E.trans (Equiv.sigmaCongrRight (fun Q => e Q)), hendpoint, ?_⟩
  · intro q j
    obtain ⟨hne, hpoly, hlc, hsub⟩ := hA q j
    refine ⟨hne, hpoly, hlc, hsub, hpoly.isClosed.isProperMap_subtypeVal, ?_, ?_⟩
    · exact (isProperMap_backwardPath_closure_admissibleBackwardDomain
        (fun _ : Fin 1 => ν) (fun _ => b) ![i (w q.val), u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
        (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν u}).comp
          (Topology.IsClosedEmbedding.inclusion hsub
            (hpoly.isClosed.preimage continuous_subtype_val)).isProperMap
    · have hn := (Finset.mem_filter.mp q.property).2
      obtain ⟨X, hX⟩ := (hne.mono hsub).of_closure
      obtain ⟨r⟩ := (nonempty_admissibleRayRealization_iff ..).mpr hX
      have hw : ν (i (w q.val)) ≠ 0 := r.transverse 0
      have hu : ν u ≠ 0 := hn ▸ hw
      intro Q hQ
      refine ⟨backwardPath_eventually_mem_halfspace
          (fun _ : Fin 1 => ν) (fun _ => b) ![i (w q.val), u] ν b hu Q,
        backwardPath_apply_zero _ _ _ ?_, ?_, ?_⟩
      · exact backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain
          _ _ _ _ _ _ _ (hsub hQ)
      · apply isProperMap_backwardPath_restrict_Iic
        have hu' : u ≠ 0 := by
          intro hz
          exact hu (by rw [hz, map_zero])
        simpa using hu'
      · exact backwardPath_singleFace_boundary hn hZ (hsub hQ)
  · intro z
    exact (C.singleFaceTransferFamilyFiberEquiv_label p a h w₀ w ν b Z hν hZ hsemi
      (E z).1 (E z).2).trans (hlabel z)

end Mei.GradedCorrespondence
