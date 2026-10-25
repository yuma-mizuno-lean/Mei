/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Exp
public import Mei.Algebra.Lie.UniversalEnveloping.CompletedLie

/-!
# BCH exponentials in finite enveloping quotients

The BCH group of a positive Lie degree truncation maps to the units of the
corresponding enveloping degree quotient. The map sends an exponential coordinate
to its finite associative exponential and commutes with lowering the cutoff.
These compatible homomorphisms compare Lie multiplication with multiplication in
the enveloping completion, even when the original Lie algebra is not nilpotent.

The construction integrates `Mei.UniversalEnvelopingAlgebra.truncatedLieToU`
using `LieHom.bchExpHom`. Nilpotence follows from the existing containment of
augmentation powers in the enveloping degree filtration. No injectivity or PBW
hypothesis is imposed.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)

-- Retain the named nilpotence predicate when passing the bound across module boundaries.
private theorem isNilpotent_augmentationImage (k : ℕ) :
    IsNilpotent ((J).map (Ideal.Quotient.mk ((F).ideal (k + 1)))) := by
  refine ⟨k + 1, ?_⟩
  simpa only [Ideal.zero_eq_bot] using
    (augmentation_map_quotient_pow_eq_bot ℒ d.degree
      (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn) k)

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Rational scalars on the enveloping algebra come from its coefficient ring. -/
local instance rationalTruncatedEnvelopingAlgebra : Algebra ℚ U :=
  Algebra.compHom U (algebraMap ℚ R)

/-- Integrate the canonical finite Lie map to units of the finite enveloping quotient. -/
noncomputable def truncatedBCHToUnits (k : ℕ) :
    BCHGroup (d.truncatedLie ℒ k) →* (U ⧸ (F).ideal (k + 1))ˣ :=
  ((truncatedLieToU d ℒ k).restrictScalars ℚ).bchExpHom
    ((J).map (Ideal.Quotient.mk ((F).ideal (k + 1))))
    (isNilpotent_augmentationImage d ℒ k)
    (fun x => by
      simpa only [LieHom.restrictScalars_apply] using truncatedLieToU_mem_map_augmentation d ℒ k x)

/-- The finite group map is the associative exponential of the canonical Lie coordinate. -/
@[simp]
theorem coe_truncatedBCHToUnits (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k)) :
    (truncatedBCHToUnits d ℒ k g : U ⧸ (F).ideal (k + 1)) =
      IsNilpotent.exp (truncatedLieToU d ℒ k (BCHGroup.log g)) := by
  unfold truncatedBCHToUnits
  rw [LieHom.coe_bchExpHom ((truncatedLieToU d ℒ k).restrictScalars ℚ),
    LieHom.restrictScalars_apply]

/-- Finite logarithms recover the canonical Lie coordinate from its integrated image. -/
@[simp↓]
theorem log_truncatedBCHToUnits (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k)) :
    IsNilpotent.log (truncatedBCHToUnits d ℒ k g : U ⧸ (F).ideal (k + 1)) =
      truncatedLieToU d ℒ k (BCHGroup.log g) := by
  unfold truncatedBCHToUnits
  rw [LieHom.log_bchExpHom ((truncatedLieToU d ℒ k).restrictScalars ℚ),
    LieHom.restrictScalars_apply]

/-- Lowering the enveloping cutoff intertwines the integrated BCH homomorphisms. -/
@[simp]
theorem factor_truncatedBCHToUnits {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.truncatedLie ℒ l)) :
    Units.map (Ideal.Quotient.factor ((F).antitone (Nat.add_le_add_right h 1)) :
        (U ⧸ (F).ideal (l + 1)) →* (U ⧸ (F).ideal (k + 1)))
        (truncatedBCHToUnits d ℒ l g) =
      truncatedBCHToUnits d ℒ k ((d.truncationMap ℒ h).bchGroupMap g) := by
  apply Units.ext
  simp only [Units.coe_map, coe_truncatedBCHToUnits, LieHom.log_bchGroupMap]
  have hn : IsNilpotent (truncatedLieToU d ℒ l (BCHGroup.log g)) :=
    Ideal.isNilpotent_of_mem _ (isNilpotent_augmentationImage d ℒ l)
      (truncatedLieToU_mem_map_augmentation d ℒ l _)
  exact (hn.map_exp (Ideal.Quotient.factor
    ((F).antitone (Nat.add_le_add_right h 1)))).trans
      (congrArg IsNilpotent.exp (factor_truncatedLieToU d ℒ h _))

end Mei.UniversalEnvelopingAlgebra
