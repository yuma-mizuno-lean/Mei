/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Logarithmic.WallFunction.Map
public import Mei.Algebra.Lie.Logarithmic.Pairing.Full
public import Mei.RingTheory.FilteredAlgebra.Positive.Basic

/-!
# Binomial function walls of the tropical vertex group

Let `μ` be an integral character of the spatial lattice, `n` a nonzero allowed degree tangent to
`μ` (that is, `μ(ρ n) = 0`) and `c` a coefficient. The tangent binomial `1 + c z^n` is congruent
to one, and its function-wall label `exp(log(1 + c z^n) ∂_μ)` is the *binomial label*
(`Mei.binomialLabel`). On a coefficient algebra `R[Q]` the binomial `1 + c z^n` is a unit of the
completion (`Mei.binomialUnit`), positive for the image of `S[Q]` when `c` is the image of an
element of `S` (`Mei.isPositive_binomialUnit`), and the binomial label multiplies a monomial
`r z^p` by `(1 + c z^n)^{μ(ρ p)}` (`Mei.completedBCHAction_binomialLabel`). A graded Lie map of
tropical vertex Lie algebras sending every tangent field `z^q ∂_μ` to `z^{T q} ∂_{μ'}` sends the
binomial label of `(μ, n, c)` to that of `(μ', T n, c)`
(`Mei.GradedLieHom.completedMap_binomialLabel`); in particular so does a tropical pairing on all
characters sending the character of `μ` to that of `μ'`
(`Mei.TropicalPairing.completedMap_binomialLabel`). Reversing the sign of the character inverts
the label (`Mei.binomialLabel_neg`).

These are the elementary wall-crossing automorphisms of the tropical vertex group of
Gross–Pandharipande–Siebert, *Quivers, curves, and the tropical vertex*, §0
(arXiv:0902.0779v3), in the formulation of Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

section Label

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (μ : Λ →+ ℤ)

/-- An allowed degree `n` with `μ(ρ n) = 0`, as an allowed degree tangent to the character `μ`
with values in `R`. -/
def binomialExponent {n : Γ} (hn : n ∈ d.monoid) (hμ : μ (ρ n) = 0) :
    tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ) :=
  ⟨n, (mem_tropicalTangentMonoid d ρ _ n).mpr ⟨hn, by simp [hμ]⟩⟩

/-- The binomial exponent is the original degree. -/
@[simp]
theorem coe_binomialExponent {n : Γ} (hn : n ∈ d.monoid) (hμ : μ (ρ n) = 0) :
    (binomialExponent (R := R) d ρ μ hn hμ : Γ) = n := (rfl)

/-- The completed tangent binomial `1 + c z^n` of a nonzero allowed degree `n` tangent to `μ` is
congruent to one. -/
theorem toCompletion_one_add_single_binomialExponent_sub_one_mem {n : Γ} (hn : n ∈ d.monoid)
    (hn0 : n ≠ 0) (hμ : μ (ρ n) = 0) (c : R) :
    (TropicalVertexCoefficientAction.filtration d
        (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ))).toCompletion
        (1 + single (binomialExponent d ρ μ hn hμ) c) - 1 ∈
      (TropicalVertexCoefficientAction.filtration d
        (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ))).completionIdeal 1 := by
  rw [← map_one (AlgFiltration.toCompletion _), ← map_sub,
    AlgFiltration.toCompletion_mem_completionIdeal_iff, add_sub_cancel_left]
  exact TropicalVertexCoefficientAction.single_mem_filtration_ideal_one d _ hn hn0 c

variable [DecidableEq Γ] [Algebra ℚ R]

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ (AddMonoidHom.comp (Int.castAddHom R) μ))

/-- The *binomial label* `exp(log(1 + c z^n) ∂_μ)` of an integral character `μ`, a nonzero allowed
degree `n` with `μ(ρ n) = 0`, and a coefficient `c`, in the completed tropical vertex group. -/
def binomialLabel {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hμ : μ (ρ n) = 0) (c : R) :
    d.completedBCHGroup ℒ :=
  d.completedBCHExp ℒ (completedTropicalTangentField d ρ ((Int.castAddHom R).comp μ)
    ((G).completedLog ⟨(G).toCompletion (1 + single (binomialExponent d ρ μ hn hμ) c),
      toCompletion_one_add_single_binomialExponent_sub_one_mem d ρ μ hn hn0 hμ c⟩))

/-- The defining logarithmic tangent field of the binomial label. -/
theorem binomialLabel_def {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hμ : μ (ρ n) = 0) (c : R) :
    binomialLabel d ρ μ hn hn0 hμ c =
      d.completedBCHExp ℒ (completedTropicalTangentField d ρ ((Int.castAddHom R).comp μ)
        ((G).completedLog ⟨(G).toCompletion (1 + single (binomialExponent d ρ μ hn hμ) c),
          toCompletion_one_add_single_binomialExponent_sub_one_mem d ρ μ hn hn0 hμ c⟩)) :=
  (rfl)

end Label

section Unit

variable {R Γ : Type*} [CommRing R] [AddCommMonoid Γ] (d : PositiveDegrees Γ)
  (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- The binomial `1 + c z^n` of a nonzero allowed degree `n`, as a unit of the completed
coefficient algebra of `R[Q]`. -/
def binomialUnit {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (c : R) : (F).completionˣ :=
  ((F).isUnit_of_sub_one_mem
    (u := 1 + (F).toCompletion (single ⟨n, (Fact.out : d.monoid ≤ Q) hn⟩ c)) (by
      rw [add_sub_cancel_left, AlgFiltration.toCompletion_mem_completionIdeal_iff]
      exact TropicalVertexCoefficientAction.single_mem_filtration_ideal_one d Q
        (q := ⟨n, (Fact.out : d.monoid ≤ Q) hn⟩) hn hn0 c)).unit

/-- The binomial unit is `1 + c z^n`. -/
@[simp]
theorem coe_binomialUnit {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (c : R) :
    (binomialUnit d Q hn hn0 c : (F).completion) =
      1 + (F).toCompletion (single ⟨n, (Fact.out : d.monoid ≤ Q) hn⟩ c) :=
  IsUnit.unit_spec _

/-- A binomial unit `1 + c z^n` whose coefficient is the image of an element of `S` under a
semiring map `φ : S →+* R` is positive for the image of `S[Q]`. -/
theorem isPositive_binomialUnit {S : Type*} [Semiring S] (φ : S →+* R) {n : Γ}
    (hn : n ∈ d.monoid) (hn0 : n ≠ 0) {c : R} (hc : c ∈ φ.rangeS) :
    (F).IsPositive (mapRingHom Q φ).rangeS (binomialUnit d Q hn hn0 c : (F).completion) := by
  obtain ⟨s, rfl⟩ := hc
  rw [coe_binomialUnit, ← map_one (F).toCompletion, ← map_add]
  exact AlgFiltration.isPositive_toCompletion
    (add_mem (one_mem _) ⟨single _ s, by rw [mapRingHom_single]⟩)

end Unit

section Action

variable {R Γ Λ : Type*} [CommRing R] [Algebra ℚ R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (μ : Λ →+ ℤ)
  (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ

/-- **Binomial wall-crossing formula.** The binomial label `exp(log(1 + c z^n) ∂_μ)` multiplies a
monomial `r z^p` of `R[Q]` by `(1 + c z^n)^{μ(ρ p)}`, the power being taken in units. -/
theorem completedBCHAction_binomialLabel {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)
    (hμ : μ (ρ n) = 0) (c : R) (p : Q) (r : R) :
    (F).completedBCHAction d ℒ (binomialLabel d ρ μ hn hn0 hμ c) ((F).toCompletion (single p r)) =
      ((binomialUnit d Q hn hn0 c ^ μ (ρ p) : (F).completionˣ) : (F).completion) *
        (F).toCompletion (single p r) := by
  rw [binomialLabel_def,
    completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog]
  congr 3
  apply Units.ext
  rw [IsUnit.unit_spec, coe_binomialUnit, completedTropicalTangentInclusion_toCompletion, map_add,
    map_one, tropicalTangentInclusion_single, map_add, map_one]
  simp only [coe_binomialExponent]

end Action

section Map

open LogarithmicVectorField

universe v w

variable {R : Type*} {Γ Γ' : Type v} {Λ Λ' : Type w} [CommRing R] [Algebra ℚ R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {T₀ : PositiveDegreeMap d e}
  (f : GradedLieHom T₀ (tropicalVertexGrading (R := R) d ρ) (tropicalVertexGrading e ρ'))
  {T : PositiveDegreeMap d e} {μ : Λ →+ ℤ} {μ' : Λ' →+ ℤ}
  (hT : (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ)).map T.toAddMonoidHom ≤
    tropicalTangentMonoid e ρ' ((Int.castAddHom R).comp μ'))
  (hf : ∀ (q : tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ)), (q : Γ) ≠ 0 →
    ∀ x : tropicalVertexLieAlgebra (R := R) d ρ,
      single ρ q ((Int.castAddHom R).comp μ) = x.val →
      (f x).val = single ρ' (T q) ((Int.castAddHom R).comp μ'))

include hT hf in
/-- A graded Lie map sending each tangent field `z^q ∂_μ` to `z^{T q} ∂_{μ'}` sends the binomial
label `exp(log(1 + c z^n) ∂_μ)` to the binomial label `exp(log(1 + c z^{n'}) ∂_{μ'})` of
`n' = T n`. -/
theorem GradedLieHom.completedMap_binomialLabel {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)
    (hμ : μ (ρ n) = 0) {n' : Γ'} (hn' : n' ∈ e.monoid) (hn0' : n' ≠ 0) (hμ' : μ' (ρ' n') = 0)
    (hTn : T n = n') (c : R) :
    f.completedMap (binomialLabel d ρ μ hn hn0 hμ c) = binomialLabel e ρ' μ' hn' hn0' hμ' c := by
  rw [binomialLabel_def, binomialLabel_def]
  refine f.completedMap_completedBCHExp_completedTropicalTangentField_completedLog hT
    (c := 1) (fun q hq x hx => by rw [one_smul]; exact hf q hq x hx) (r := 1)
    (by rw [Nat.cast_one, one_mul]) _ _ ?_
  rw [pow_one, completedTropicalTangentMap_toCompletion, map_add, map_one,
    tropicalTangentMap_single]
  congr 3
  exact Subtype.ext hTn

end Map

section Neg

variable {R : Type*} {Γ : Type v} {Λ : Type w} [CommRing R] [Algebra ℚ R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [DecidableEq Γ] {d : PositiveDegrees Γ} {ρ : Γ →+ Λ}
  {μ : Λ →+ ℤ}

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ (AddMonoidHom.comp (Int.castAddHom R) μ))

local notation "G'" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ (AddMonoidHom.comp (Int.castAddHom R) (-μ)))

/-- Reversing the sign of the character inverts the binomial label:
`exp(log(1 + c z^n) ∂_{-μ}) = exp(log(1 + c z^n) ∂_μ)⁻¹`. The tangency `(-μ)(ρ n) = 0` is
a consequence of `μ(ρ n) = 0`. -/
@[simp]
theorem binomialLabel_neg {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hμ : μ (ρ n) = 0) (c : R) :
    binomialLabel d ρ (-μ) hn hn0 (by simp [hμ]) c = (binomialLabel d ρ μ hn hn0 hμ c)⁻¹ := by
  have hμ' : (-μ) (ρ n) = 0 := by simp [hμ]
  -- The identity map sends each field `z^q ∂_μ` to `-z^q ∂_{-μ}`, hence the label of `μ` to the
  -- inverse of the label of `-μ`.
  have hneg : (Int.castAddHom R).comp (-μ) = -((Int.castAddHom R).comp μ) := by
    ext x
    simp
  have hT : (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ)).map
      (PositiveDegreeMap.id d).toAddMonoidHom ≤
      tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (-μ)) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [SetLike.mem_coe, mem_tropicalTangentMonoid] at hq
    simpa [mem_tropicalTangentMonoid] using hq
  have hf : ∀ q : tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ), (q : Γ) ≠ 0 →
      ∀ x : tropicalVertexLieAlgebra (R := R) d ρ,
        LogarithmicVectorField.single ρ q ((Int.castAddHom R).comp μ) = x.val →
        (GradedLieHom.id (d := d) (tropicalVertexGrading (R := R) d ρ) x).val =
          (-1 : R) • LogarithmicVectorField.single ρ (PositiveDegreeMap.id d q)
            ((Int.castAddHom R).comp (-μ)) := by
    intro q _ x hx
    simp [← hx, hneg]
  have h := GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField
    (GradedLieHom.id (d := d) (tropicalVertexGrading (R := R) d ρ)) hT hf
    ((G).completedLog ⟨(G).toCompletion (1 + single (binomialExponent d ρ μ hn hμ) c),
      toCompletion_one_add_single_binomialExponent_sub_one_mem d ρ μ hn hn0 hμ c⟩)
  rw [GradedLieHom.completedMap_id, completedTropicalTangentMap_completedLog] at h
  have he : (⟨completedTropicalTangentMap (PositiveDegreeMap.id d) hT
      ((G).toCompletion (1 + single (binomialExponent d ρ μ hn hμ) c)),
      completedTropicalTangentMap_sub_one_mem (PositiveDegreeMap.id d) hT
        (toCompletion_one_add_single_binomialExponent_sub_one_mem d ρ μ hn hn0 hμ c)⟩ :
      {u : (G').completion // u - 1 ∈ (G').completionIdeal 1}) =
      ⟨(G').toCompletion (1 + single (binomialExponent d ρ (-μ) hn hμ') c),
        toCompletion_one_add_single_binomialExponent_sub_one_mem d ρ (-μ) hn hn0 hμ' c⟩ := by
    apply Subtype.ext
    simp only [completedTropicalTangentMap_toCompletion, map_add, map_one,
      tropicalTangentMap_single]
    congr 3
    exact Subtype.ext (by simp)
  dsimp only at h
  rw [he, MonoidHom.id_apply, map_smul, neg_one_smul] at h
  rw [binomialLabel_def, binomialLabel_def, h, PositiveDegrees.completedBCHExp_neg, inv_inv]

end Neg

section Pairing

universe v w

variable {R : Type*} {Γ Γ' : Type v} {Λ Λ' : Type w} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') (⊤ : Submodule R (Λ →+ R)))

/-- A pairing on all characters sends the allowed degrees tangent to a character `m` to allowed
degrees tangent to its image `S m`. -/
theorem TropicalPairing.map_tropicalTangentMonoid_le (m : Λ →+ R) :
    (tropicalTangentMonoid d ρ m).map p.degreeMap.toAddMonoidHom ≤
      tropicalTangentMonoid e ρ' (p.characterMap ⟨m, Submodule.mem_top⟩) := by
  rintro _ ⟨q, hq, rfl⟩
  rw [SetLike.mem_coe, mem_tropicalTangentMonoid] at hq
  rw [mem_tropicalTangentMonoid]
  exact ⟨p.degreeMap.map_mem hq.1, (p.eval_eq _ hq.1).trans hq.2⟩

variable [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ']

/-- A pairing on all characters sending the character of `μ` to that of `μ'` sends the binomial
label `exp(log(1 + c z^n) ∂_μ)` to the binomial label `exp(log(1 + c z^{n'}) ∂_{μ'})` of the image
`n' = T n`. -/
theorem TropicalPairing.completedMap_binomialLabel {μ : Λ →+ ℤ} {μ' : Λ' →+ ℤ}
    (hS : p.characterMap ⟨(Int.castAddHom R).comp μ, Submodule.mem_top⟩ =
      (Int.castAddHom R).comp μ')
    {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hμ : μ (ρ n) = 0) {n' : Γ'} (hn' : n' ∈ e.monoid)
    (hn0' : n' ≠ 0) (hμ' : μ' (ρ' n') = 0) (hTn : p.degreeMap n = n') (c : R) :
    p.tropicalVertexGradedLieHom.completedMap (binomialLabel d ρ μ hn hn0 hμ c) =
      binomialLabel e ρ' μ' hn' hn0' hμ' c :=
  p.tropicalVertexGradedLieHom.completedMap_binomialLabel (T := p.degreeMap)
    (by rw [← hS]; exact p.map_tropicalTangentMonoid_le _)
    (fun _ _ x hx => by rw [p.coe_tropicalVertexGradedLieHom_of_homogeneous x _ hx, hS])
    hn hn0 hμ hn' hn0' hμ' hTn c

end Pairing

end Mei
