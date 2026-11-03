/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallSpace
public import Mei.Geometry.ScatteringDiagram.WallSpace.Map
public import TauCeti.Algebra.DirectSum.Internal

/-!
# The base quotient of a module probe

The module probe is a split extension of the base Lie algebra by the abelian ideal of
coefficients. The base Lie algebra, regarded as graded by `Γ × ℤ` and concentrated in
charge zero, is the quotient of the probe by this ideal: the projection onto the base kills
exactly the elements with zero base part. Projection onto the base and inclusion of the base
are fixed-degree graded Lie maps for the probe's positive degree data, and the image of the
probe wall spaces under the projection gives wall spaces on the quotient. This is the
split-extension setting of `DirectedDiagram.relativeScat`.

We use `LieAlgebra.SemiDirectSum.projr`, `DirectedWallSpaces.map` and
`DirectSum.IsInternal.iSup_fiber`, following Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section

namespace Mei.ModuleProbe

section Grading

variable {R Γ L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L)

open Classical in
/-- A Lie grading by `Γ`, regarded as a grading by `Γ × ℤ` concentrated in charge zero. -/
def baseGrading (a : Γ × ℤ) : Submodule R L := if a.2 = 0 then ℒ a.1 else ⊥

open Classical in
/-- The defining charge cases of the charge-zero regrading. -/
theorem baseGrading_def (a : Γ × ℤ) :
    baseGrading ℒ a = if a.2 = 0 then ℒ a.1 else ⊥ := (rfl)

/-- Charge zero recovers the original homogeneous piece. -/
@[simp]
theorem baseGrading_zero (q : Γ) : baseGrading ℒ (q, 0) = ℒ q := by
  simp [baseGrading]

/-- Every nonzero charge has zero homogeneous piece. -/
@[simp]
theorem baseGrading_of_ne_zero (q : Γ) {c : ℤ} (hc : c ≠ 0) : baseGrading ℒ (q, c) = ⊥ := by
  simp [baseGrading, hc]

section Bracket

variable [AddCommMonoid Γ]

/-- The charge-zero regrading respects the Lie bracket. -/
instance instGradedBracketBaseGrading [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (baseGrading ℒ) (baseGrading ℒ) where
  bracket_mem := by
    rintro ⟨n, c⟩ ⟨q, e⟩ x y hx hy
    by_cases hc : c = 0
    · by_cases he : e = 0
      · subst hc he
        rw [baseGrading_zero] at hx hy
        simpa using SetLike.GradedBracket.bracket_mem hx hy
      · rw [baseGrading_of_ne_zero ℒ q he, Submodule.mem_bot] at hy
        rw [hy, lie_zero]
        exact Submodule.zero_mem _
    · rw [baseGrading_of_ne_zero ℒ n hc, Submodule.mem_bot] at hx
      rw [hx, zero_lie]
      exact Submodule.zero_mem _

end Bracket

private theorem baseGrading_eq_iSup (a : Γ × ℤ) :
    baseGrading ℒ a = ⨆ i, ⨆ (_ : (i, (0 : ℤ)) = a), ℒ i := by
  rcases a with ⟨q, c⟩
  by_cases hc : c = 0
  · subst hc
    apply le_antisymm
    · rw [baseGrading_zero]
      exact le_iSup_of_le q (le_iSup_of_le rfl le_rfl)
    · refine iSup_le fun i => iSup_le fun hi => ?_
      obtain rfl := congrArg Prod.fst hi
      simp
  · rw [baseGrading_of_ne_zero ℒ q hc]
    refine (bot_le.antisymm ?_)
    refine le_bot_iff.mpr ?_
    simp only [iSup_eq_bot]
    intro i hi
    exact (hc (congrArg Prod.snd hi).symm).elim

section Decomposition

variable [AddCommMonoid Γ] [DecidableEq Γ] [DirectSum.Decomposition ℒ]

/-- The charge-zero regrading inherits the internal decomposition. -/
instance instDecompositionBaseGrading : DirectSum.Decomposition (baseGrading ℒ) :=
  -- The ascription elaborates the internality argument as a proof, allowing the private
  -- helper in this public data declaration; a tactic `have` rejects that helper.
  (show DirectSum.IsInternal (baseGrading ℒ) from by
    have h := (DirectSum.Decomposition.isInternal ℒ).iSup_fiber
      (fun i => (i, (0 : ℤ)))
    simpa only [← baseGrading_eq_iSup] using h).chooseDecomposition

end Decomposition

/-- The charge-zero regrading of a Lie grading is a Lie grading. -/
instance instGradedLieAlgebraBaseGrading [AddCommMonoid Γ] [DecidableEq Γ] [GradedLieAlgebra ℒ] :
    GradedLieAlgebra (baseGrading ℒ) where
  toDecomposition := inferInstance
  toGradedBracket := inferInstance

end Grading

section Projection

variable {R M Γ Λ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

/-- The charge-zero regrading is positive for the probe's degree data. -/
instance instIsPositiveGradingBaseGrading :
    IsPositiveGrading (positiveDegrees d p) (baseGrading ℒ) where
  eq_bot := by
    rintro ⟨q, c⟩ h
    by_cases hc : c = 0
    · subst hc
      rw [baseGrading_zero, IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) q]
      simpa using h
    · exact baseGrading_of_ne_zero ℒ q hc

/-- Projection of the probe onto its base quotient, preserving the extended degree. -/
def baseProjection :
    GradedLieHom (PositiveDegreeMap.id (positiveDegrees d p))
      (grading d ℳ p ℒ) (baseGrading ℒ) where
  toLieHom := LieAlgebra.SemiDirectSum.projr _
  map_mem := by
    rintro ⟨q, c⟩ x hx
    simp only [PositiveDegreeMap.id_apply]
    by_cases h₀ : c = 0
    · subst h₀
      rw [baseGrading_zero]
      exact ((mem_grading_base d ℳ p ℒ q x).mp hx).2
    · rw [baseGrading_of_ne_zero ℒ q h₀]
      by_cases h₁ : c = 1
      · subst h₁
        rw [Submodule.mem_bot]
        exact ((mem_grading_module d ℳ p ℒ q x).mp hx).1
      · have hx₀ : x = 0 := by
          simpa only [grading_def, h₀, h₁, ↓reduceIte, Submodule.mem_bot] using hx
        rw [hx₀]
        exact Submodule.zero_mem _

/-- The projection keeps the base part of a probe element. -/
@[simp]
theorem baseProjection_apply (x : ProbeLie d ℳ p ℒ) : baseProjection d ℳ p ℒ x = x.right := (rfl)

/-- Inclusion of the base into the probe, preserving the extended degree. -/
def baseSection :
    GradedLieHom (PositiveDegreeMap.id (positiveDegrees d p))
      (baseGrading ℒ) (grading d ℳ p ℒ) where
  toLieHom := baseInclusion d ℳ p ℒ
  map_mem := by
    rintro ⟨q, c⟩ x hx
    simp only [PositiveDegreeMap.id_apply]
    by_cases h₀ : c = 0
    · subst h₀
      rw [baseGrading_zero] at hx
      rw [grading_base]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    · rw [baseGrading_of_ne_zero ℒ q h₀, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _

/-- The section is the charge-zero inclusion of the base. -/
@[simp]
theorem baseSection_apply (x : L) : baseSection d ℳ p ℒ x = baseInclusion d ℳ p ℒ x := (rfl)

/-- Including the base in the probe and projecting recovers the base. -/
theorem baseProjection_baseSection (x : L) : baseProjection d ℳ p ℒ (baseSection d ℳ p ℒ x) = x :=
  LieAlgebra.SemiDirectSum.projr_inr_apply _

/-- Including the base in the probe after projecting forgets the module summand. -/
theorem baseSection_baseProjection (x : ProbeLie d ℳ p ℒ) :
    baseSection d ℳ p ℒ (baseProjection d ℳ p ℒ x) = chargeZeroGradedLieHom d ℳ p ℒ x := by
  rw [baseSection_apply, baseProjection_apply, chargeZeroGradedLieHom_apply]

/-- The composite of projection and section is the identity on the base quotient. -/
theorem baseProjection_compId_baseSection :
    (baseProjection d ℳ p ℒ).compId (baseSection d ℳ p ℒ) = GradedLieHom.id (baseGrading ℒ) :=
  DFunLike.ext _ _ fun x => by simp

/-- The composite of section and projection is the charge-zero endomorphism of the probe. -/
theorem baseSection_compId_baseProjection :
    (baseSection d ℳ p ℒ).compId (baseProjection d ℳ p ℒ) = chargeZeroGradedLieHom d ℳ p ℒ :=
  DFunLike.ext _ _ fun x => by simp

variable {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]

/-- The wall spaces of the base quotient of a module probe, the image of the probe wall
spaces under the projection. -/
def baseWallSpaces : DirectedWallSpaces (spatialMap ρ) (baseGrading ℒ) :=
  (wallSpaces d ℳ p ℒ H).map (baseProjection d ℳ p ℒ).toLieHom (baseGrading ℒ)
    fun a => by
      rintro _ ⟨x, hx, rfl⟩
      simpa using (baseProjection d ℳ p ℒ).map_mem (n := a) hx

/-- The wall spaces of the base quotient are the images of the probe wall spaces. -/
@[simp]
theorem baseWallSpaces_wall (a : Γ × ℤ) (m : (Λ × ℤ × ℤ) →+ ℤ) :
    (baseWallSpaces d ℳ p ℒ H).wall a m =
      ((wallSpaces d ℳ p ℒ H).wall a m).map (baseProjection d ℳ p ℒ).toLieHom.toLinearMap := by
  simp only [baseWallSpaces, DirectedWallSpaces.map_wall]

/-- Projection carries probe wall elements to wall elements of the base quotient. -/
theorem baseProjection_mem_baseWallSpaces {a : Γ × ℤ} {m : (Λ × ℤ × ℤ) →+ ℤ}
    {x : ProbeLie d ℳ p ℒ} (hx : x ∈ (wallSpaces d ℳ p ℒ H).wall a m) :
    baseProjection d ℳ p ℒ x ∈ (baseWallSpaces d ℳ p ℒ H).wall a m := by
  rw [baseWallSpaces_wall]
  exact Submodule.mem_map_of_mem hx

/-- The section carries wall elements of the base quotient to probe wall elements. -/
theorem baseSection_mem_wallSpaces {a : Γ × ℤ} {m : (Λ × ℤ × ℤ) →+ ℤ} {y : L}
    (hy : y ∈ (baseWallSpaces d ℳ p ℒ H).wall a m) :
    baseSection d ℳ p ℒ y ∈ (wallSpaces d ℳ p ℒ H).wall a m := by
  rw [baseWallSpaces_wall] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H a m x hx

end Projection

end Mei.ModuleProbe
