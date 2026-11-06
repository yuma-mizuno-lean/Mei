/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Family
public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Coefficient
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Reindex

/-!
# Coefficient embeddings of single-face closed families

An injective output degree map and an injective output coefficient map identify
single-face transfer families between possibly different chamber modules.
The identification uses the entire inventory of nonzero whole transfers, even
when some endpoint domains are empty. It preserves the endpoint domains and
continuous path extensions, including the incoming half-line and all singular
and terminal degenerations. Consequently both families admit the same closed
polyhedral charts, with proper endpoint and path maps.

This combines the correspondence transfer comparison with the existing
single-face closed-family construction. No inverse on the ambient degree set,
injectivity of a face leg, or finite generation of a chamber module is needed.
We follow Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4), for whole-component propagation,
and Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2), for closed endpoint charts.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.GradedCorrespondence.Hom

variable {R B U M B' U' M' ι κ ι' κ' V Λ : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid B'] [Module R B'] [AddCommMonoid U'] [Module R U']
  [AddCommMonoid M'] [Module R M'] [DecidableEq κ] [DecidableEq κ']
  {𝒰 : ι → Submodule R U} {ℳ : κ → Submodule R M}
  {𝒰' : ι' → Submodule R U'} {𝓝 : κ' → Submodule R M'}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  {I : Set ι} {J : Set κ} {I' : Set ι'} {J' : Set κ'}
  {C : GradedCorrespondence (B := B) 𝒰 ℳ I J}
  {D : GradedCorrespondence (B := B') 𝒰' 𝓝 I' J'}
  {σ : ι → ι'} {τ : κ → κ'}
  (f : Hom C D σ τ) (p : I) (a : 𝒰 p)
  (hτ : Function.Injective τ) (hinj : Function.Injective f.right)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Λ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (w₀ : Λ) (v : κ → Λ) (w : κ' → Λ) (hv : ∀ q, w (τ q) = v q)
  (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)
  (hν : Toric.IsRationalFunctional h ν.toLinearMap)
  (hZ : Z ⊆ {x | ν x = b}) (hsemi : IsRationalSemilinear h Z)

local notation "p'" => (Subtype.mk (σ p) (f.admissible_left p.property) : I')
local notation "a'" => (Subtype.mk (f.left a) (f.left_mem p a a.property) : 𝒰' p')
local notation "labels" => (Finset.filter (fun q => ν (i (v q)) = ν (i w₀))
  (DFinsupp.support (DirectSum.decompose ℳ (C.right (C.liftLeft p a)))) : Type _)
local notation "E" => f.singleFaceTransferLabelEquivOfInjective p (i w₀)
  (fun q => i (v q)) (fun q => i (w q)) (fun q => congrArg i (hv q)) ν a hτ hinj
local notation "F" => C.singleFaceTransferFamily p a h w₀ v ν b Z hν hZ hsemi
local notation "G" => D.singleFaceTransferFamily p' a' h w₀ w ν b Z hν hZ hsemi
local notation "sourcePath" q:max =>
  backwardPath (fun _ : Fin 1 => ν) (fun _ => b) ![i (v q), i w₀]
local notation "targetPath" q:max =>
  backwardPath (fun _ : Fin 1 => ν) (fun _ => b) ![i (w q), i w₀]

open Classical in
/-- The complete semilinear families agree after the proved change of output
labels. Their domains retain source admission and singular avoidance. -/
theorem singleFaceTransferFamily_reindex : (G).reindex E = F := by
  apply FiniteSemilinearFamily.ext
  · intro q
    simp only [FiniteSemilinearFamily.reindex_domain, singleFaceTransferFamily_domain,
      singleFaceTransferLabelEquivOfInjective_degree, hv]
  · intro q Q hG hF
    simp only [FiniteSemilinearFamily.reindex_eval, singleFaceTransferFamily_eval]

open Classical in
/-- One closed polyhedral subdivision simultaneously presents both embedded
families. The chart sets, disjoint interiors, coverage, proper endpoint maps and
proper whole-path extensions are shared. Boundary paths need not be admissible. -/
theorem exists_singleFaceTransferFamily_commonClosedCharts :
    ∃ (η : labels → Type) (_ : ∀ q, Finite (η q)) (A : ∀ q, η q → Set V),
      (∀ q j, (A q j).Nonempty ∧ IsRationalNormalPolyhedron h (A q j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A q j)) ∧
        A q j ⊆ closure ((F).domain q) ∧
        A q j ⊆ closure ((G).domain (E q)) ∧
        IsProperMap (fun Q : A q j => (Q : V)) ∧
        IsProperMap (fun Q : A q j => (sourcePath q.val) Q.val) ∧
        IsProperMap (fun Q : A q j => (targetPath (E q).val) Q.val)) ∧
      (∀ q, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (A q j))
        (intrinsicInterior ℝ (A q l))) ∧
      (∀ q, ⋃ j, intrinsicInterior ℝ (A q j) = (F).domain q) ∧
      (∀ q, ⋃ j, intrinsicInterior ℝ (A q j) = (G).domain (E q)) := by
  obtain ⟨η, hη, A, hA, hdisj, hcover, _⟩ :=
    C.exists_singleFaceTransferFamily_closedCharts p a h w₀ v ν b Z hν hZ hsemi
  have hD (q : labels) : (G).domain (E q) = (F).domain q := by
    simpa only [FiniteSemilinearFamily.reindex_domain] using
      congrArg (fun H => H.domain q)
        (f.singleFaceTransferFamily_reindex p a hτ hinj h w₀ v w hv ν b Z hν hZ hsemi)
  refine ⟨η, hη, A, ?_, hdisj, ?_, ?_⟩
  · intro q j
    obtain ⟨hne, hpoly, hlc, hsub, hend, hpath, _⟩ := hA q j
    have hsub' : A q j ⊆ closure ((F).domain q) := by
      simpa only [singleFaceTransferFamily_domain] using hsub
    refine ⟨hne, hpoly, hlc, hsub', ?_, hend, hpath, ?_⟩
    · simpa only [hD, singleFaceTransferFamily_domain] using hsub
    · rw [f.singleFaceTransferLabelEquivOfInjective_path p (i w₀)
        (fun q => i (v q)) (fun q => i (w q)) (fun q => congrArg i (hv q)) ν b a hτ hinj q]
      exact hpath
  · simpa only [singleFaceTransferFamily_domain] using hcover
  · intro q
    simpa only [hD, singleFaceTransferFamily_domain] using hcover q

end Mei.GradedCorrespondence.Hom
