/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal.Resolution
public import Mei.Algebra.Category.SemimoduleCat.Multispan.Basic

/-!
# Matching coefficients of finite terminal slab evaluations

The common semilinear families of actual incoming, crossing and constant
contributions near a regular slab point assemble into
one matching coefficient family on the slab span. The chamber identities use
the complete closed-chart incident resolutions on the two sides. The common total terminal lift
determines its face value, the sum of theta monomials with their original incoming
parameter maps.

This is matching at one coefficient face. It does not supply the closed global
broken-line family, its singular-degeneration certificate or sheaf descent.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Mei.FocusFocus

open AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- The full-exponent slab correspondence as a multispan of semimodules.
The false and true chamber indices denote its negative and positive sides. -/
abbrev slabTerminalMultispan (t : R) :
    MultispanIndex (MultispanShape.ofLinearOrder Bool) (SemimoduleCat R) where
  left _ := SemimoduleCat.of R (TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)))
  right _ := SemimoduleCat.of R (R[ℤ × ℤ])
  fst _ := SemimoduleCat.ofHom (exponentLeftMap (C t * (1 + T 1))).toLinearMap
  snd _ := SemimoduleCat.ofHom (exponentRightMap (C t * (1 + T 1))).toLinearMap

private theorem terminalShape_fst (c : (MultispanShape.ofLinearOrder Bool).L) :
    (MultispanShape.ofLinearOrder Bool).fst c = false := by
  have hc : c = default := Subsingleton.elim _ _
  subst c
  rfl

private theorem terminalShape_snd (c : (MultispanShape.ofLinearOrder Bool).L) :
    (MultispanShape.ofLinearOrder Bool).snd c = true := by
  have hc : c = default := Subsingleton.elim _ _
  subst c
  rfl

/-- Both maps together are injective, even for nilpotent smoothing parameters. -/
theorem slabTerminalMultispan_jointly_injective (t : R)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    Function.Injective (((slabTerminalMultispan t).fst c).hom.prod
      ((slabTerminalMultispan t).snd c).hom) :=
  exponentMaps_jointly_injective (C t * (1 + T 1))

variable {ι H : Type*} [AddCommMonoid H] [Module R H]
  (s : Finset ι) (n b : ι → ℤ) (t : R) (α : ι → H →ₗ[R] R)
  (h : TauCeti.Toric.IsIntegralLattice
    ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {v : ℝ} {L U : ℝ × ℝ}

private def terminalChamberMap (side : Bool) : H →ₗ[R] R[ℤ × ℤ] :=
  (if side then (exponentRightMap (C t * (1 + T 1))).toLinearMap else
    (exponentLeftMap (C t * (1 + T 1))).toLinearMap).comp
      (slabTerminalFiniteLift s n b t α)

private theorem terminalChamberMap_false :
    terminalChamberMap s n b t α false =
      (exponentLeftMap (C t * (1 + T 1))).toLinearMap.comp
        (slabTerminalFiniteLift s n b t α) := (rfl)

private theorem terminalChamberMap_true :
    terminalChamberMap s n b t α true =
      (exponentRightMap (C t * (1 + T 1))).toLinearMap.comp
        (slabTerminalFiniteLift s n b t α) := (rfl)

private theorem terminalChamberMap_eq
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (a : H) (side : Bool) :
    terminalChamberMap s n b t α side a =
      ∑ i ∈ s, (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) (if side then U else L) := by
  have expand (Q : ℝ × ℝ) (hQ : Q ∈ slabTerminalFiniteDomain s n b v)
      (side : Bool) (hs : Q ∈ incomingSlabDomain side) (i : ι) (hi : i ∈ s) :
      (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) Q =
        (if side then exponentRightMap (C t * (1 + T 1)) else
          exponentLeftMap (C t * (1 + T 1))) (α i a • theta t (n i) (b i)) := by
    have hQi := (mem_slabTerminalFiniteDomain s n b v Q).mp hQ i hi
    rw [slabThetaFamily_weightedEvaluation_eq_terminal_resolution
      t (α i a) (n i) (b i) h hQi side hs,
      slabThetaTerminalResolution_weightedSum t (α i a) (n i) (b i) (by
        have hp := (mem_slabTerminalDomain (n i) (b i) v Q).mp hQi ⟨0, by omega⟩
        exact left_ne_zero_of_mul hp.ne') side]
  cases side
  · simp only [terminalChamberMap_false, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Bool.false_eq_true, ↓reduceIte, slabTerminalFiniteLift_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (expand L hL false (by simpa using hLs) i hi).symm
  · simp only [terminalChamberMap_true, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      ↓reduceIte, slabTerminalFiniteLift_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (expand U hU true (by simpa using hUs) i hi).symm

/-- Common-family weighted evaluations at any two opposite-side endpoints in
the common terminal neighborhood extend uniquely to a linear matching family. -/
theorem existsUnique_slabTerminalFinite_matchingFamily
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1) :
    ∃! ℓ : H →ₗ[R] SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan,
      ∀ a (side : Bool), (ℓ a).val (.right side) =
        ∑ i ∈ s, (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) (if side then U else L) := by
  have htest : ∃! ℓ : H →ₗ[R]
      SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan,
      ∀ a side, (ℓ a).val (.right side) = terminalChamberMap s n b t α side a := by
    apply ((slabTerminalMultispan t).existsUnique_sections_lift_iff
      (terminalChamberMap s n b t α) (slabTerminalMultispan_jointly_injective t)).mpr
    intro a c
    refine ⟨slabTerminalFiniteLift s n b t α a, Prod.ext ?_ ?_⟩
    · simp only [LinearMap.prod_apply, Function.prod_apply, SemimoduleCat.hom_ofHom,
        terminalShape_fst, terminalChamberMap_false, LinearMap.comp_apply]
    · simp only [LinearMap.prod_apply, Function.prod_apply, SemimoduleCat.hom_ofHom,
        terminalShape_snd, terminalChamberMap_true, LinearMap.comp_apply]
  obtain ⟨ℓ, hℓ, huniq⟩ := htest
  refine ⟨ℓ, fun a side => (hℓ a side).trans
    (terminalChamberMap_eq s n b t α h hL hU hLs hUs a side), ?_⟩
  intro l hl
  apply huniq l
  intro a side
  exact (hl a side).trans (terminalChamberMap_eq s n b t α h hL hU hLs hUs a side).symm

/-- The face coefficient of any matching extension of the actual evaluations
is the common total theta lift, with complete incoming records still indexed by `s`. -/
theorem slabTerminalFinite_matchingFamily_face
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (ℓ : H →ₗ[R] SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan)
    (hℓ : ∀ a (side : Bool), (ℓ a).val (.right side) =
      ∑ i ∈ s, (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) (if side then U else L))
    (a : H) (c : (MultispanShape.ofLinearOrder Bool).L) :
    (ℓ a).val (.left c) = slabTerminalFiniteLift s n b t α a := by
  have hface := (slabTerminalMultispan t).mem_sectionsSubmodule_multispan.mp (ℓ a).property
  have hleft := (hface.1 c).trans
    (congrArg (fun side : Bool => (ℓ a).val (.right side)) (terminalShape_fst c))
  have hright := (hface.2 c).trans
    (congrArg (fun side : Bool => (ℓ a).val (.right side)) (terminalShape_snd c))
  have hvalueL : (ℓ a).val (.right false) =
      ∑ i ∈ s, (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) L := by
    simpa only [Bool.false_eq_true, ↓reduceIte, slabThetaFamily_weightedEvaluation] using hℓ a false
  have hvalueR : (ℓ a).val (.right true) =
      ∑ i ∈ s, (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) U := by
    simpa only [↓reduceIte] using hℓ a true
  apply exponentMaps_jointly_injective (C t * (1 + T 1))
  exact Prod.ext
    ((hleft.trans hvalueL).trans
      (by simpa only [slabThetaFamily_weightedEvaluation] using
        (exponentLeftMap_slabTerminalFiniteLift s n b t α hL hLs a).symm))
    ((hright.trans hvalueR).trans
      (by simpa only [slabThetaFamily_weightedEvaluation] using
        (exponentRightMap_slabTerminalFiniteLift s n b t α hU hUs a).symm))

end Mei.FocusFocus
