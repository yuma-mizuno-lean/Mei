/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Covariance.Basic

/-!
# Cutoff comparison of directed equivalence

Agreement at one cutoff descends to every lower cutoff by specializing coordinate
covariance to the identity spatial and wall-space coordinate changes. If the degree
ideal vanishes at a cutoff, agreement there detects full diagram equivalence.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe uι uκ

variable {Γ Λ R L V : Type*} {ι : Type uι} {κ : Type uκ}
  [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h H ι}
  {E : DirectedDiagram (d := d) h H κ}

/-- Agreement at a higher cutoff implies agreement at every lower cutoff.
The lower-order test paths may meet walls that are active only at the higher order. -/
theorem LevelEquivalent.mono {k l : ℕ} (hDE : D.LevelEquivalent E l) (hkl : k ≤ l) :
    D.LevelEquivalent E k := by
  have ha : (DirectedWallSpaces.CoordinateChange.refl (d := d) H).degreeMap.modulus k ≤ l :=
    ((DirectedWallSpaces.CoordinateChange.refl H).degreeMap_modulus_le_iff k l).mpr
      fun n _ hn => by
        simpa only [DirectedWallSpaces.CoordinateChange.refl_degreeEquiv, AddEquiv.refl_apply]
          using hn.trans (Int.ofNat_le.mpr hkl)
  simpa only [image_refl] using hDE.image
    (e := Toric.IntegralAffineEquiv.refl h)
    (E := DirectedWallSpaces.CoordinateChange.refl H) (hE := by simp) ha

/-- If no Lie degrees remain above order `k`, that order detects diagram equivalence.
No consistency hypothesis is required. -/
theorem equivalent_iff_levelEquivalent_of_degreeIdeal_eq_bot
    (D : DirectedDiagram (d := d) h H ι) (E : DirectedDiagram (d := d) h H κ)
    {k : ℕ} (hk : d.degreeIdeal ℒ k = ⊥) :
    D.Equivalent E ↔ D.LevelEquivalent E k := by
  rw [equivalent_iff]
  refine ⟨fun hDE => hDE k, fun hDE l => ?_⟩
  obtain hlk | hkl := le_total l k
  · exact hDE.mono hlk
  · have hinj : Function.Injective (d.truncationMap ℒ hkl) := by
      rw [← LieHom.ker_eq_bot, PositiveDegrees.truncationMap_def, LieIdeal.ker_factor, hk]
      simp
    rw [levelEquivalent_def] at hDE ⊢
    intro x y x' y' p q hpq
    apply LieHom.bchGroupMap_injective hinj
    rw [D.truncation_levelPathProduct hkl, E.truncation_levelPathProduct hkl]
    apply hDE
    exact (WallComplement.vertices_restrictPrefunctor _
      (Set.inclusion (D.active_mono hkl)) p).trans
        (hpq.trans (WallComplement.vertices_restrictPrefunctor _
          (Set.inclusion (E.active_mono hkl)) q).symm)

end Mei.DirectedDiagram
