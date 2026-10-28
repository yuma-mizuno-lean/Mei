/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Lie
public import Mei.Algebra.QuantumMonoidAlgebra.Positive
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.Algebra.Lie.Filtered.Inner

/-!
# Inner actions on positive quantum coefficients

The strictly positive quantum Lie algebra embeds in the positive coefficient
algebra. Its commutator action raises the degree filtration, and hence integrates
to algebra automorphisms of the completed coefficient algebra. The coefficient
image of a completed label's logarithm lies in the first completion ideal.
Every completed label acts by conjugation with its completed exponential;
finite projections compute this formula by nilpotent exponentials.

Open `Mei.QuantumMonoidAlgebra.CoefficientAction` to select the inner action, and
use `AlgFiltration.completedBCHAction` with `positiveFiltration` and
`positiveLieGrading`. The action uses Mathlib's `LieRingModule.compLieHom`;
integration and conjugation use `AlgFiltration.completedBCHAction` and
`AlgFiltration.expAction_apply_eq_completedExp_mul`. The finite inclusions follow
`Mei.UniversalEnvelopingAlgebra.truncatedLieToU`;
compatibility of logarithms uses `PositiveDegrees.completedBCHExp`.
The parallel enveloping construction is `UniversalEnvelopingAlgebra.InnerAction`.
The quantum inner action follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(iii), arXiv:1503.06183.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

/-- A strictly positive quantum Lie element is also a positive coefficient. -/
theorem positiveLieAlgebra_le_positiveSubalgebra :
    (positiveLieAlgebra q β d).toSubmodule ≤
      (positiveSubalgebra q β d.monoid).toSubmodule := by
  classical
  intro x hx
  rw [Subalgebra.mem_toSubmodule, mem_positiveSubalgebra_iff]
  intro n hn
  exact (decompose_eq_zero_iff q β x n).mp
    (Subtype.ext ((mem_positiveLieAlgebra_iff q β d x).mp hx n (Or.inl hn)))

/-- The inclusion of strictly positive Lie elements into positive quantum coefficients. -/
def positiveLieToCoefficients : positiveLieAlgebra q β d →ₗ⁅R⁆
    positiveSubalgebra q β d.monoid :=
  { (positiveLieAlgebra q β d).incl.toLinearMap.codRestrict
      (positiveSubalgebra q β d.monoid).toSubmodule
      (fun x => positiveLieAlgebra_le_positiveSubalgebra q β d x.property) with
    map_lie' {x y} := by
      apply Subtype.ext
      exact LieSubalgebra.coe_bracket (positiveLieAlgebra q β d) x y }

/-- The coefficient inclusion retains the original ambient quantum element. -/
@[simp]
theorem coe_positiveLieToCoefficients (x : positiveLieAlgebra q β d) :
    (positiveLieToCoefficients q β d x : QuantumMonoidAlgebra q β) = x := (rfl)

local notation "𝓕" => positiveFiltration q β d.monoid d.degree
  (fun _ hn => d.degree_nonneg hn)
local notation "ℒ" => positiveLieGrading q β d

namespace CoefficientAction

/-- The positive quantum Lie algebra acts on positive coefficients by commutators.
Open this scope to select this action. -/
scoped instance instLieRingModule : LieRingModule (positiveLieAlgebra q β d)
    (positiveSubalgebra q β d.monoid) :=
  LieRingModule.compLieHom _ (positiveLieToCoefficients q β d)

/-- The quantum inner action is linear over its coefficient ring. -/
scoped instance instLieModule : LieModule R (positiveLieAlgebra q β d)
    (positiveSubalgebra q β d.monoid) :=
  LieModule.compLieHom _ (positiveLieToCoefficients q β d)

/-- The selected action is the associative commutator with the Lie element's inclusion. -/
@[simp]
theorem lie_eq (x : positiveLieAlgebra q β d) (a : positiveSubalgebra q β d.monoid) :
    ⁅x, a⁆ = positiveLieToCoefficients q β d x * a -
      a * positiveLieToCoefficients q β d x := by
  rw [LieRingModule.compLieHom_apply, Ring.lie_def]

/-- Quantum commutators satisfy the associative Leibniz rule. -/
scoped instance instIsDerivationAction : IsDerivationAction (positiveLieAlgebra q β d)
    (positiveSubalgebra q β d.monoid) where
  lie_mul x a b := by simp [lie_eq, mul_sub, sub_mul, mul_assoc]

end CoefficientAction

/-- A Lie degree tail embeds in the corresponding successor coefficient ideal. -/
theorem positiveLieToCoefficients_mem_positiveFiltration {k : ℕ}
    {x : positiveLieAlgebra q β d} (hx : x ∈ d.degreeSubmodule ℒ k) :
    positiveLieToCoefficients q β d x ∈ (𝓕).ideal (k + 1) := by
  classical
  rw [d.degreeSubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => positiveLieToCoefficients q β d x ∈ (𝓕).ideal (k + 1))
    hx ?_ (by simp) ?_
  · intro n x hx
    rw [mem_positiveFiltration_iff]
    intro p hp
    obtain ⟨r, hr⟩ := (mem_grade_iff q β n x).mp ((mem_positiveLieGrading q β d n x).mp hx)
    have hnp : n.val ≠ p := by
      intro he
      have := n.property
      rw [he] at this
      omega
    simp only [coe_positiveLieToCoefficients, ← hr, ← basis_apply, map_smul,
      Module.Basis.repr_self]
    simp [hnp]
  · intro x y hx hy
    simpa only [map_add] using ((𝓕).ideal (k + 1)).add_mem hx hy

variable [DecidableEq Γ]

/-- The positive Lie inclusion descends to the matching finite coefficient quotient. -/
def truncatedCoefficientInclusion (k : ℕ) : d.truncatedLie ℒ k →ₗ⁅R⁆
    (positiveSubalgebra q β d.monoid) ⧸ (𝓕).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ
    (((Ideal.Quotient.mkₐ R ((𝓕).ideal (k + 1))).toLieHom).comp
      (positiveLieToCoefficients q β d)) (by
        intro x hx
        rw [LieHom.mem_ker, LieHom.comp_apply, AlgHom.toLieHom_apply,
          Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        apply positiveLieToCoefficients_mem_positiveFiltration q β d
        rw [← d.degreeIdeal_toSubmodule ℒ k]
        exact hx)

/-- The finite inclusion sends a Lie representative to its coefficient class. -/
@[simp]
theorem truncatedCoefficientInclusion_mk (k : ℕ) (x : positiveLieAlgebra q β d) :
    truncatedCoefficientInclusion q β d k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk _ (positiveLieToCoefficients q β d x) := by
  simp [truncatedCoefficientInclusion, LieHom.comp_apply]

/-- Lie truncation and coefficient truncation commute with the finite inclusion. -/
@[simp]
theorem factor_truncatedCoefficientInclusion {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) :
    Ideal.Quotient.factor ((𝓕).antitone (Nat.add_le_add_right h 1))
        (truncatedCoefficientInclusion q β d l x) =
      truncatedCoefficientInclusion q β d k (d.truncationMap ℒ h x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp

namespace CoefficientAction

/-- The positive quantum inner action raises the coefficient degree filtration. -/
scoped instance instIsFiltrationRaising :
    IsFiltrationRaising d ℒ ((𝓕).toModuleFiltration R) where
  lie_mem {a b x y} hx hy := by
    have hi := positiveLieToCoefficients_mem_positiveFiltration q β d hx
    rw [lie_eq]
    exact ((𝓕).ideal (a + b + 1)).sub_mem
      (by simpa only [Nat.add_assoc, Nat.add_comm 1] using (𝓕).mul_mem hi hy)
      (by simpa only [Nat.add_comm b, Nat.add_assoc] using (𝓕).mul_mem hy hi)

variable [Algebra ℚ R]

/-- Rational scalars on the ambient quantum algebra are inherited from `R`. -/
scoped instance ambientRationalAlgebra : Algebra ℚ (QuantumMonoidAlgebra q β) :=
  Algebra.compHom _ (algebraMap ℚ R)

private theorem factor_coefficientLog (g : d.completedBCHGroup ℒ) {k l : ℕ} (h : k ≤ l) :
    Ideal.Quotient.factor ((𝓕).antitone (Nat.add_le_add_right h 1))
        (truncatedCoefficientInclusion q β d l (BCHGroup.log (CompletedGroup.projection l g))) =
      truncatedCoefficientInclusion q β d k (BCHGroup.log (CompletedGroup.projection k g)) := by
  let z := (d.completedBCHExp ℒ).symm g
  let π := LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
  have ht : d.truncationMap ℒ h (BCHGroup.log (CompletedGroup.projection l g)) =
      BCHGroup.log (CompletedGroup.projection k g) := calc
    _ = d.truncationMap ℒ h (π l z) :=
      congrArg (d.truncationMap ℒ h) (d.completionProjection_completedBCHExp_symm ℒ l g).symm
    _ = π k z := by
      simpa only [PositiveDegrees.truncationMap_def] using
        LieIdeal.factor_completionProjection _ _ h z
    _ = _ := d.completionProjection_completedBCHExp_symm ℒ k g
  exact (factor_truncatedCoefficientInclusion q β d h _).trans
    (congrArg (truncatedCoefficientInclusion q β d k) ht)

/-- The coefficient image of a completed label's logarithm. It lies in the first
completion ideal, so its completed exponential is defined. -/
def completedCoefficientLog (g : d.completedBCHGroup ℒ) : (𝓕).completionIdeal 1 := by
  let z : (𝓕).completion := ⟨fun k => truncatedCoefficientInclusion q β d k.unop
      (BCHGroup.log (CompletedGroup.projection k.unop g)),
    ((𝓕).mem_completion_iff _).mpr (fun h => factor_coefficientLog q β d g h)⟩
  refine ⟨z, ?_⟩
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker]
  have hz : BCHGroup.log (CompletedGroup.projection 0 g) = 0 := Subsingleton.elim _ _
  simp only [AlgFiltration.projection_apply, z, hz, map_zero]

/-- Every projection reads the coefficient image of the finite logarithm. -/
@[simp]
theorem projection_completedCoefficientLog (g : d.completedBCHGroup ℒ) (k : ℕ) :
    (𝓕).projection k (completedCoefficientLog q β d g) =
      truncatedCoefficientInclusion q β d k (BCHGroup.log (CompletedGroup.projection k g)) :=
  (𝓕).projection_apply k (completedCoefficientLog q β d g)

/-- On an original Lie exponential, the coefficient logarithm is the canonical
completed image of the original quantum coefficient. -/
@[simp]
theorem coe_completedCoefficientLog_expToCompletion (x : positiveLieAlgebra q β d) :
    (completedCoefficientLog q β d (d.expToCompletion ℒ x) : (𝓕).completion) =
      (𝓕).toCompletion (positiveLieToCoefficients q β d x) := by
  apply (𝓕).completion_ext
  intro k
  simp

/-- Inverting a completed label negates its coefficient logarithm. -/
@[simp]
theorem coe_completedCoefficientLog_inv (g : d.completedBCHGroup ℒ) :
    (completedCoefficientLog q β d g⁻¹ : (𝓕).completion) =
      -(completedCoefficientLog q β d g : (𝓕).completion) := by
  apply (𝓕).completion_ext
  intro k
  have hg : BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g⁻¹) =
      -BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) :=
    (congrArg (BCHGroup.log (L := d.truncatedLie ℒ k))
      ((CompletedGroup.projection (F := d.groupTower ℒ) k).map_inv g)).trans
        (BCHGroup.log_inv (CompletedGroup.projection k g))
  calc
    _ = truncatedCoefficientInclusion q β d k
        (BCHGroup.log (CompletedGroup.projection k g⁻¹)) :=
      projection_completedCoefficientLog q β d g⁻¹ k
    _ = -truncatedCoefficientInclusion q β d k
        (BCHGroup.log (CompletedGroup.projection k g)) :=
      (congrArg (truncatedCoefficientInclusion q β d k) hg).trans (map_neg _ _)
    _ = -((𝓕).projection k (completedCoefficientLog q β d g)) :=
      congrArg Neg.neg (projection_completedCoefficientLog q β d g k).symm
    _ = _ := (((𝓕).projection k).toAddMonoidHom.map_neg _).symm

/-- At each cutoff, the inner exponential is conjugation by the exponential of
the finite coefficient inclusion. -/
@[simp]
theorem truncatedExpLieAction_apply (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : (positiveSubalgebra q β d.monoid) ⧸ (𝓕).ideal (k + 1)) :
    (𝓕).truncatedExpLieAction d ℒ k x a =
      IsNilpotent.exp (truncatedCoefficientInclusion q β d k x) * a *
        IsNilpotent.exp (-truncatedCoefficientInclusion q β d k x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, AlgFiltration.truncatedExpLieAction_mk,
    truncatedCoefficientInclusion_mk]
  exact (𝓕).quotientExpLieAction_apply_eq_exp_mul_exp_neg d ℒ k (lie_eq q β d x)
    (positiveLieToCoefficients_mem_positiveFiltration q β d (by simp)) a

/-- Every completed quantum BCH label acts by conjugation with the completed
exponential of its coefficient logarithm. The inverse factor uses the inverse label. -/
@[simp]
theorem completedBCHAction_apply (g : d.completedBCHGroup ℒ) (a : (𝓕).completion) :
    (𝓕).completedBCHAction d ℒ g a =
      (𝓕).completedExp (completedCoefficientLog q β d g) * a *
        (𝓕).completedExp (completedCoefficientLog q β d g⁻¹) := by
  apply (𝓕).completion_ext
  intro k
  let x : d.truncatedLie ℒ k := BCHGroup.log (CompletedGroup.projection k g)
  have hg : (𝓕).projection k (completedCoefficientLog q β d g) =
      truncatedCoefficientInclusion q β d k x := projection_completedCoefficientLog q β d g k
  have hgi : (𝓕).projection k (completedCoefficientLog q β d g⁻¹) =
      -truncatedCoefficientInclusion q β d k x := by
    exact (congrArg ((𝓕).projection k) (coe_completedCoefficientLog_inv q β d g)).trans
      ((((𝓕).projection k).toAddMonoidHom.map_neg _).trans (congrArg Neg.neg hg))
  calc
    _ = (𝓕).truncatedExpLieAction d ℒ k x ((𝓕).projection k a) :=
      (𝓕).projection_completedBCHAction d ℒ g a k
    _ = IsNilpotent.exp (truncatedCoefficientInclusion q β d k x) * (𝓕).projection k a *
        IsNilpotent.exp (-truncatedCoefficientInclusion q β d k x) :=
      truncatedExpLieAction_apply q β d k x _
    _ = _ := by
      let u := (𝓕).completedExp (completedCoefficientLog q β d g)
      let v := (𝓕).completedExp (completedCoefficientLog q β d g⁻¹)
      have hu : (𝓕).projection k u =
          IsNilpotent.exp (truncatedCoefficientInclusion q β d k x) :=
        ((𝓕).projection_completedExp _ k).trans (congrArg IsNilpotent.exp hg)
      have hv : (𝓕).projection k v =
          IsNilpotent.exp (-truncatedCoefficientInclusion q β d k x) :=
        ((𝓕).projection_completedExp _ k).trans (congrArg IsNilpotent.exp hgi)
      exact ((((𝓕).projection k).toMonoidHom.map_mul (u * a) v).trans
        ((congrArg (fun t => t * (𝓕).projection k v)
          (((𝓕).projection k).toMonoidHom.map_mul u a)).trans
            (congrArg₂ (fun u v => u * (𝓕).projection k a * v) hu hv))).symm

end CoefficientAction
end Mei.QuantumMonoidAlgebra
