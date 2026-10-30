/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic

/-!
# Incoming diagrams of BLM polynomial inputs

The polynomial `1 + ∑ₛ pᵢₛ z^(s wᵢ)` generally has logarithmic terms on
several supported rays of the finite alphabet lattice. We realize its logarithm
as a completed tangent field, split its exponential into ray labels, and place
the tangent ray labels on the full cylinder over `eᵢ⊥`. These infinitely indexed
walls have finite activity at every cutoff and are all incoming. Their products
recover the original label at each finite order, whose coefficient action is
the prescribed polynomial function raised to the normal pairing.

The constructions use `PositiveDegrees.rayFactor`, its wall-group and finite
support theorems, and `DirectedWall.ofLinearHyperplane`. The polynomial inputs
and their ray presentations follow Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams*, §8.1 and §9.2 (arXiv:2503.03719v1), and the
function-wall convention of Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra

variable {N ι R V : Type*} [AddCommGroup N]
  {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι} (I : B.BLMPolynomialInput)

variable [DecidableEq ι]

local notation "Γ" => Module.Dual ℤ N × (I.Letter → ℤ)
local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "ρ" => AddMonoidHom.id Γ

/-- The primitive cylinder normal: evaluate the spatial character on `eᵢ`,
ignoring the coefficient-variable coordinates. -/
def alphabetNormal (i : B.unfrozenIndex) : Γ →+ ℤ where
  toFun q := q.1 (B.basis i)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq ι] in
@[simp]
theorem alphabetNormal_apply (i : B.unfrozenIndex) (q : Γ) :
    I.alphabetNormal i q = q.1 (B.basis i) := (rfl)

omit [DecidableEq ι] in
/-- Evaluation on a basis vector is a nonzero integral normal. -/
theorem alphabetNormal_ne_zero (i : B.unfrozenIndex) : I.alphabetNormal i ≠ 0 := by
  intro he
  have h := DFunLike.congr_fun he (B.basis.coord i, 0)
  simp at h

variable [CommRing R]

local notation "χ" i => AddMonoidHom.comp (Int.castAddHom R) (I.alphabetNormal i)
local notation "T" i => tropicalTangentMonoid 𝒅 ρ (χ i)
local notation "F" i => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 (T i)
local notation "ℒ" => tropicalVertexGrading (R := R) 𝒅 ρ
local notation "H" => tropicalVertexWallSpaces (R := R) 𝒅 ρ

/-- A variable monomial, regarded as a tangent degree of its initial wall. -/
private def tangentLetter (i : B.unfrozenIndex) (s : Fin (I.multiplicity i)) : T i :=
  ⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
    (mem_tropicalTangentMonoid _ _ _ _).mpr
      ⟨PositiveDegrees.letter_mem _ _, by simp⟩⟩

@[simp]
private theorem coe_tangentLetter (i : B.unfrozenIndex) (s : Fin (I.multiplicity i)) :
    (I.tangentLetter (R := R) i s : Γ) =
      PositiveDegrees.letter I.letterExponent ⟨i, s⟩ := (rfl)

/-- The initial polynomial in its tangent coefficient algebra. Its inclusion
in the ambient alphabet algebra is `initialFunction`. -/
def tangentInitialFunction (i : B.unfrozenIndex) : R[T i] :=
  1 + ∑ s : Fin (I.multiplicity i), single (I.tangentLetter i s) 1

/-- Forgetting the tangent subtype recovers the original polynomial, including
all independent coefficient letters. -/
@[simp]
theorem mapDomain_tangentInitialFunction (i : B.unfrozenIndex) :
    mapDomain (fun q : T i => q.val) (I.tangentInitialFunction (R := R) i) =
      I.initialFunction R i := by
  have he : mapDomainRingHom R (T i).subtype (I.tangentInitialFunction (R := R) i) =
      I.initialFunction R i := by
    simp only [tangentInitialFunction, initialFunction_def, map_add, map_one, map_sum,
      mapDomainRingHom_apply, mapDomain_single, AddSubmonoid.subtype_apply, coe_tangentLetter]
  simpa only [mapDomainRingHom_apply, AddSubmonoid.coe_subtype] using he

/-- The initial polynomial is one modulo the first tangent filtration ideal. -/
theorem tangentInitialFunction_sub_one_mem (i : B.unfrozenIndex) :
    I.tangentInitialFunction (R := R) i - 1 ∈ (F i).ideal 1 := by
  rw [tangentInitialFunction, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  refine Or.inr ⟨I.tangentLetter i s, PositiveDegrees.letter_mem _ _, ?_, 0, by simp⟩
  simp [PositiveDegrees.finiteAlphabet_degree, PositiveDegrees.letter_snd]

/-- The completed initial polynomial is congruent to one. -/
theorem toCompletion_tangentInitialFunction_sub_one_mem (i : B.unfrozenIndex) :
    (F i).toCompletion (I.tangentInitialFunction (R := R) i) - 1 ∈
      (F i).completionIdeal 1 := by
  rw [← map_one (F i).toCompletion, ← map_sub,
    AlgFiltration.toCompletion_mem_completionIdeal_iff]
  exact I.tangentInitialFunction_sub_one_mem i

variable [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R]

/-- The unsplit function-wall label `exp(log(fᵢ) ∂_(eᵢ))` in the completed
tropical vertex group of the finite alphabet. -/
def initialLabel (i : B.unfrozenIndex) : (𝒅).completedBCHGroup ℒ :=
  (𝒅).completedBCHExp ℒ (completedTropicalTangentField 𝒅 ρ (χ i)
    ((F i).completedLog ⟨(F i).toCompletion (I.tangentInitialFunction i),
      I.toCompletion_tangentInitialFunction_sub_one_mem i⟩))

/-- The defining logarithmic tangent field of the combined initial label. -/
theorem initialLabel_def (i : B.unfrozenIndex) :
    I.initialLabel (R := R) i =
      (𝒅).completedBCHExp ℒ (completedTropicalTangentField 𝒅 ρ (χ i)
        ((F i).completedLog ⟨(F i).toCompletion (I.tangentInitialFunction i),
          I.toCompletion_tangentInitialFunction_sub_one_mem i⟩)) := (rfl)

section Action

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid (Module.Dual ℤ N × (I.Letter → ℤ)))
  [Fact ((PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 Q

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- In any coefficient monoid containing the positive degrees, the tangent
polynomial becomes the same finite sum of its independent variable monomials. -/
theorem tropicalTangentInclusion_tangentInitialFunction (i : B.unfrozenIndex) :
    tropicalTangentInclusion 𝒅 ρ (χ i) Q Fact.out (I.tangentInitialFunction i) =
      1 + ∑ s : Fin (I.multiplicity i),
        single (⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
          (Fact.out : (PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)
            (PositiveDegrees.letter_mem _ _)⟩ : Q) 1 := by
  simp only [tangentInitialFunction, map_add, map_one, map_sum,
    tropicalTangentInclusion_single, coe_tangentLetter]

/-- The combined initial label acts by the original polynomial raised to the
integral cylinder-normal pairing. Negative pairings use inverse unit powers. -/
theorem completedBCHAction_initialLabel (i : B.unfrozenIndex)
    (f : (G).completionˣ)
    (hf : (f : (G).completion) = (G).toCompletion
      (1 + ∑ s : Fin (I.multiplicity i),
        single (⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
          (Fact.out : (PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)
            (PositiveDegrees.letter_mem _ _)⟩ : Q) 1))
    (p : Q) (c : R) :
    (G).completedBCHAction 𝒅 ℒ (I.initialLabel i) ((G).toCompletion (single p c)) =
      (f ^ I.alphabetNormal i p.val : (G).completionˣ) *
        (G).toCompletion (single p c) := by
  have he := completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog
    𝒅 ρ Q (I.alphabetNormal i) (I.toCompletion_tangentInitialFunction_sub_one_mem i) p c
  rw [← initialLabel] at he
  have hf' : (isUnit_completedTropicalTangentInclusion 𝒅 ρ (χ i) Q
      (I.toCompletion_tangentInitialFunction_sub_one_mem i)).unit = f := by
    apply Units.ext
    rw [IsUnit.unit_spec, completedTropicalTangentInclusion_toCompletion,
      I.tropicalTangentInclusion_tangentInitialFunction Q i, hf]
  simpa only [AddMonoidHom.id_apply, hf'] using he

end Action

/-- Each ray factor is an actual wall-group label, even when the ray generator
does not belong to the positive monoid. -/
@[simp high]
theorem rayFactor_initialLabel_mem_wallGroup (i : B.unfrozenIndex) (w : SupportedRay 𝒅) :
    (𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w ∈ (H).wallGroup w (I.alphabetNormal i) :=
  rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ _

/-- Nontangent rays have identity labels and can be omitted from the diagram. -/
@[simp]
theorem rayFactor_initialLabel_eq_one (i : B.unfrozenIndex) {w : SupportedRay 𝒅}
    (hw : w.generator.1 (B.basis i) ≠ 0) :
    (𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w = 1 :=
  rayFactor_completedBCHExp_completedTropicalTangentField_eq_one _ _ _ _ hw

/-- The ray labels belonging to a fixed initial polynomial commute. -/
theorem commute_rayFactor_initialLabel (i : B.unfrozenIndex) (v w : SupportedRay 𝒅) :
    Commute ((𝒅).rayFactor ℒ (I.initialLabel (R := R) i) v)
      ((𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w) :=
  (H).commute_of_mem_wallGroup (I.rayFactor_initialLabel_mem_wallGroup i v)
    (I.rayFactor_initialLabel_mem_wallGroup i w) one_ne_zero one_ne_zero rfl

private theorem projection_initialLabel_eq_noncommProd [Module.Finite ℤ N]
    (i : B.unfrozenIndex) (k : ℕ) (s : Finset (SupportedRay 𝒅))
    (hs : (𝒅).raysAtOrder k ⊆ s) :
    CompletedGroup.projection k (I.initialLabel (R := R) i) =
      s.noncommProd (fun w => CompletedGroup.projection k
        ((𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w))
        (fun v _ w _ _ => (I.commute_rayFactor_initialLabel i v w).map _) := by
  let := Module.Free.of_basis B.basis
  exact projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_rayFactor
    𝒅 ρ (I.alphabetNormal i) _ k s hs

/-- The walls are indexed by the original unfrozen index and a tangent supported
ray. Coincident supports from different original polynomials remain distinct. -/
abbrev IncomingIndex : Type _ := Σ i : B.unfrozenIndex,
  {w : SupportedRay (PositiveDegrees.finiteAlphabet I.letterExponent) //
    I.alphabetNormal i w.generator = 0}

variable [Module.Finite ℤ N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ N × (I.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The incoming BLM diagram on the finite alphabet lattice. Each polynomial
is split into supported-ray labels on its full cylinder hyperplane. -/
def incomingDiagram : DirectedDiagram (d := 𝒅) h (H) I.IncomingIndex where
  wall j := DirectedWall.ofLinearHyperplane h (H) (I.alphabetNormal j.1)
    (I.alphabetNormal_ne_zero j.1) j.2.val j.2.property
    ⟨(𝒅).rayFactor ℒ (I.initialLabel j.1) j.2.val,
      I.rayFactor_initialLabel_mem_wallGroup j.1 j.2.val⟩
  finite_active k := by
    let := Module.Free.of_basis B.basis
    let : HasUniqueDiv (Module.Dual ℤ N × (I.Letter → ℤ)) :=
      .of_isTorsionFree ℤ _
    let f : I.IncomingIndex → B.unfrozenIndex × SupportedRay 𝒅 := fun j => (j.1, j.2.val)
    have hf : Function.Injective f := by
      rintro ⟨i, v⟩ ⟨j, w⟩ he
      obtain ⟨rfl, he⟩ := Prod.mk.inj he
      exact congrArg (Sigma.mk i) (Subtype.ext he)
    apply ((Set.finite_univ.prod ((𝒅).finite_raysAtOrder k)).preimage hf.injOn).subset
    intro j hj
    refine ⟨Set.mem_univ _, ?_⟩
    by_contra hw
    apply hj
    simpa only [DirectedWall.ofLinearHyperplane_label] using
      (𝒅).projection_eq_one_of_notMem_raysAtOrder ℒ
        ((𝒅).rayFactor_mem_completedRaySubgroup ℒ (I.initialLabel j.1) j.2.val) k hw

@[simp]
theorem incomingDiagram_normal (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).normal = I.alphabetNormal j.1 := by
  simp [incomingDiagram]

@[simp]
theorem incomingDiagram_ray (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).ray = j.2.val := by
  simp [incomingDiagram]

@[simp]
theorem incomingDiagram_support (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).support =
      (h.realCharacter (I.alphabetNormal j.1)).ker := by
  simp [incomingDiagram]

@[simp]
theorem incomingDiagram_label (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).label =
      (𝒅).rayFactor ℒ (I.initialLabel (R := R) j.1) j.2.val := by
  simp [incomingDiagram]

/-- At every cutoff, the labels on the tangent rays of the actual incoming
diagram reassemble the original polynomial label. The finite set may contain
additional rays, whose surviving factors are retained automatically. -/
theorem projection_initialLabel_eq_noncommProd_incomingDiagram
    (i : B.unfrozenIndex) (k : ℕ)
    (s : Finset {w : SupportedRay 𝒅 // I.alphabetNormal i w.generator = 0})
    (hs : ∀ w ∈ (𝒅).raysAtOrder k, ∀ hw : I.alphabetNormal i w.generator = 0,
      ⟨w, hw⟩ ∈ s) :
    CompletedGroup.projection k (I.initialLabel (R := R) i) =
      s.noncommProd (fun w => CompletedGroup.projection k
        ((I.incomingDiagram (R := R) h).wall ⟨i, w⟩).label)
        (fun v _ w _ _ => by
          simp only [incomingDiagram_label]
          exact (I.commute_rayFactor_initialLabel i v.val w.val).map _) := by
  classical
  let := Module.Free.of_basis B.basis
  let : HasUniqueDiv (Module.Dual ℤ N × (I.Letter → ℤ)) :=
    .of_isTorsionFree ℤ _
  let e : {w : SupportedRay 𝒅 // I.alphabetNormal i w.generator = 0} ↪ SupportedRay 𝒅 :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let t := (𝒅).finite_raysAtOrder k |>.toFinset
  let f (w : SupportedRay 𝒅) :=
    CompletedGroup.projection k ((𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w)
  have comm : (↑(s.map e ∪ t) : Set (SupportedRay 𝒅)).Pairwise
      (fun v w => Commute (f v) (f w)) :=
    fun v _ w _ _ => (I.commute_rayFactor_initialLabel i v w).map _
  rw [I.projection_initialLabel_eq_noncommProd i k (s.map e ∪ t) (by simp [t])]
  rw [← Finset.noncommProd_subset Finset.subset_union_left f comm (fun w hw hn => ?_),
    Finset.noncommProd_map]
  · exact Finset.noncommProd_congr rfl (fun w _ => by
      simp [f, e, incomingDiagram_label]) _
  · have hwt : w ∈ (𝒅).raysAtOrder k := by
      simpa only [Finset.mem_union, hn, false_or, t, Set.Finite.mem_toFinset] using hw
    have hnormal : I.alphabetNormal i w.generator ≠ 0 := by
      intro hzero
      exact hn (Finset.mem_map.mpr ⟨⟨w, hzero⟩, hs w hwt hzero, rfl⟩)
    simp only [f, I.rayFactor_initialLabel_eq_one i hnormal, map_one]

/-- Every wall is incoming, with no constraint on the skew form's radical. -/
@[simp]
theorem incomingDiagram_incoming (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).Incoming :=
  DirectedWall.ofLinearHyperplane_incoming _ _ _ _ _ _ _

/-- The full-hyperplane condition required for outgoing completion. -/
theorem incomingDiagram_full (j : I.IncomingIndex) :
    ∃ c : ℝ, ((I.incomingDiagram (R := R) h).wall j).support =
      {x | h.realCharacter ((I.incomingDiagram (R := R) h).wall j).normal x = c} :=
  ⟨0, by
    simp only [incomingDiagram_support, incomingDiagram_normal]
    exact Set.ext fun _ => LinearMap.mem_ker⟩

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
