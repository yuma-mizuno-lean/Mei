/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Completion
public import Mei.Algebra.Lie.Graded.Shifted.Map

/-!
# Naturality of completed weighted ray evaluation

A degree-preserving coefficient map equivariant along a graded Lie homomorphism
commutes with the actual finite ray sums and their completed evaluation. The
signed propagation maps are the BCH actions induced by the original Lie actions;
their compatibility is derived from Lie equivariance. Coefficient maps may kill
whole decorations, including the incoming coefficient. The finite comparison
discards exactly those rays whose final decorations vanish.

The encounter alphabet, supports, singular sets and incoming source are fixed.
No consistency or genericity hypothesis is needed, and homogeneous coefficient
modules need not be free or finite. Every encounter is retained even if its label
specializes to the identity. Comparing inventories after deleting inactive walls
is a separate geometric question.

We use `map_cutoffDecoratedEvaluation`, the shifted coefficient quotient maps,
and `shiftedQuotientMap_truncatedBCHAction`. The completed comparison follows by
the projections of `completedBCHCutoffEvaluation` and `shiftedCompletionMap`.
This is coefficient naturality for the whole-component broken-line construction
of Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Definition 2.10 and Theorem 2.14 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R M N V J K : Type*} {L L' : Type u}
  [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L' N] [LieModule R L' N]
  (d : PositiveDegrees Γ)
  (ℒ : Γ → Submodule R L) (ℒ' : Γ → Submodule R L')
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℒ'] [IsPositiveGrading d ℒ']
  (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ' 𝓝]
  (p : Γ) (φ : GradedLieHom (PositiveDegreeMap.id d) ℒ ℒ')
  (ψ : M →ₗ[R] N) (hψ : ∀ q, ℳ q ≤ (𝓝 q).comap ψ)
  (hequiv : ∀ (x : L) (a : M), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

local notation "I" => PositiveDegreeMap.id d
-- Use the public identity-map equations rather than unfolding its opaque definition.
local notation "hψ'" => fun q => Eq.mpr
  (congrArg (fun n => ℳ q ≤ Submodule.comap ψ (𝓝 n)) (PositiveDegreeMap.id_apply (d := d) q)) (hψ q)
local notation "μ" => PositiveDegreeMap.modulus I
local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "F'" => d.shiftedLieFiltration ℒ' 𝓝 (I p)
local notation "G" => fun k => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "G'" => fun k =>
  TauCeti.InternalGrading.piece (d.shiftedQuotientGrading 𝓝 (I p) k)
local notation "qψ" => PositiveDegreeMap.shiftedQuotientMap I ℳ 𝓝 p ψ hψ'
local notation "sψ" => PositiveDegreeMap.shiftedMap I ℳ 𝓝 p ψ hψ'
local notation "T" => fun k (g : J → d.truncatedGroup ℒ k) j =>
  LinearEquiv.toLinearMap (ModuleFiltration.truncatedBCHAction (F) d ℒ k (g j))
local notation "U" => fun k (g : J → d.truncatedGroup ℒ' k) j =>
  LinearEquiv.toLinearMap (ModuleFiltration.truncatedBCHAction (F') d ℒ' k (g j))

include hequiv

/-- Equivariant homogeneous coefficient maps commute with the actual weighted
ray sum at each finite order. The source order is the identity degree map's
modulus, which equals the target order. Target labels are induced by the Lie map. -/
theorem map_cutoffDecoratedEvaluation_shiftedBCHAction
    (k : ℕ) (g : J → d.truncatedGroup ℒ (μ k)) (a : G (μ k) 0) :
    qψ k (cutoffDecoratedEvaluation d (G (μ k)) (T (μ k) g)
        a v f c ε P W S C k Q) =
      cutoffDecoratedEvaluation d (G' k)
        (U k (fun j => (φ.truncatedMap k le_rfl).bchGroupMap (g j)))
        ⟨qψ k a, by simpa only [map_zero] using
          (I).shiftedQuotientMap_mem_shiftedQuotientGrading ℳ 𝓝 p ψ hψ' k a.property⟩
        v f c ε P W S C k Q := by
  apply map_cutoffDecoratedEvaluation d (G (μ k)) (G' k) (qψ k)
    (fun n x hx => by simpa only [PositiveDegreeMap.id_apply] using
      (I).shiftedQuotientMap_mem_shiftedQuotientGrading ℳ 𝓝 p ψ hψ' k hx)
  intro j
  exact LinearMap.ext fun x => (I).shiftedQuotientMap_truncatedBCHAction
    ℳ 𝓝 p φ ψ hψ' hequiv k (g j) x

local notation "input" => fun k (a : shiftedGrading ℳ d.monoid p 0) =>
  (Subtype.mk (Submodule.Quotient.mk (a : shiftedSubmodule ℳ d.monoid p))
    (Iff.mpr (d.mem_shiftedQuotientGrading_iff ℳ p)
      (Exists.intro a (And.intro (Subtype.property a) rfl))) : G k 0)
local notation "input'" => fun k (a : shiftedGrading 𝓝 d.monoid (I p) 0) =>
  (Subtype.mk (Submodule.Quotient.mk (a : shiftedSubmodule 𝓝 d.monoid (I p)))
    (Iff.mpr (d.mem_shiftedQuotientGrading_iff 𝓝 (I p))
      (Exists.intro a (And.intro (Subtype.property a) rfl))) : G' k 0)
local notation "aψ" => fun a : shiftedGrading ℳ d.monoid p 0 =>
  (Subtype.mk (sψ a)
    (Eq.mp (congrArg (fun n => sψ a ∈ shiftedGrading 𝓝 d.monoid (I p) n)
      (PositiveDegreeMap.id_apply (d := d) 0))
      (PositiveDegreeMap.shiftedMap_mem_shiftedGrading I ℳ 𝓝 p ψ hψ' (Subtype.property a))) :
        shiftedGrading 𝓝 d.monoid (I p) 0)

/-- For compatible completed labels, every finite evaluation specializes to
that of the completed image labels and the original image input. -/
theorem map_cutoffDecoratedEvaluation_completedBCHAction
    (k : ℕ) (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0) :
    qψ k (cutoffDecoratedEvaluation d (G (μ k))
        (T (μ k) (fun j => CompletedGroup.projection (μ k) (g j)))
        (input (μ k) a) v f c ε P W S C (μ k) Q) =
      cutoffDecoratedEvaluation d (G' k)
        (U k (fun j => CompletedGroup.projection k (φ.completedMap (g j))))
        (input' k (aψ a)) v f c ε P W S C k Q := by
  have hg (j : J) :
      (φ.truncatedMap k le_rfl).bchGroupMap (CompletedGroup.projection (μ k) (g j)) =
        CompletedGroup.projection k (φ.completedMap (g j)) :=
    (φ.projection_completedMap_of_le k le_rfl (g j)).symm
  have ha : (⟨qψ k (input (μ k) a), by
      simpa only [map_zero] using (I).shiftedQuotientMap_mem_shiftedQuotientGrading
        ℳ 𝓝 p ψ hψ' k (input (μ k) a).property⟩ : G' k 0) =
      input' k (aψ a) := by
    apply Subtype.ext
    exact (I).shiftedQuotientMap_mk ℳ 𝓝 p ψ hψ' k a
  simpa only [hg, ha, PositiveDegreeMap.id_modulus] using
    d.map_cutoffDecoratedEvaluation_shiftedBCHAction ℒ ℒ' ℳ 𝓝 p φ ψ hψ hequiv
      v f c ε P W S C Q k
      (fun j => CompletedGroup.projection (μ k) (g j)) (input (μ k) a)

/-- The existing map of shifted coefficient completions commutes with the
completed weighted evaluation over all encounter itineraries. This allows
noninjective Lie and coefficient maps, vanished inputs and zero spatial shifts. -/
theorem map_completedBCHCutoffEvaluation
    (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0) :
    (I).shiftedCompletionMap ℳ 𝓝 p ψ hψ'
        (d.completedBCHCutoffEvaluation ℒ ℳ p v f c ε P W S C Q g a) =
      d.completedBCHCutoffEvaluation ℒ' 𝓝 (I p) v f c ε P W S C Q
        (fun j => φ.completedMap (g j)) (aψ a) := by
  apply (F').completion_ext
  intro k
  rw [PositiveDegreeMap.projection_shiftedCompletionMap,
    projection_completedBCHCutoffEvaluation, projection_completedBCHCutoffEvaluation]
  exact d.map_cutoffDecoratedEvaluation_completedBCHAction ℒ ℒ' ℳ 𝓝 p φ ψ hψ hequiv
    v f c ε P W S C Q k g a

end Mei.PositiveDegrees
