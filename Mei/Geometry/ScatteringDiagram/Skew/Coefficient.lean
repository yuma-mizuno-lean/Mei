/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Embedding
public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.Algebra.Lie.Filtered.Map

/-!
# Principal coefficient actions

The positive skew Lie algebra acts on the principal coefficient monoid
`M° × P` by logarithmic derivations. The action of degree `n` shifts exponents
by `(p₁*(n), n)` and evaluates the character coordinate on `n`. The
positive-increment filtration is exactly the degree filtration on the second
coordinate, so this action integrates on its completion.

Open the `Mei.SkewLatticeDatum.PrincipalCoefficientAction` scope to use the
Lie module and filtration instances with `AlgFiltration.completedBCHAction`
and `AlgFiltration.completedBCHAction_injective`.
The resulting representation is faithful when the ambient integer module is
projective, in particular for every lattice. No spanning assumption on `P`
or nondegeneracy assumption on the skew form is needed.
It is the completed tropical vertex action of the principal image of the group,
so an element of the completed skew group is determined by the action of its
principal image on the monomials `z^p`.

The construction composes `principalGradedLieHom` with
`tropicalVertexCoefficientAction`; it retains radical degrees even when the skew
form is zero. The principal realization follows Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open _root_.AddMonoidAlgebra

variable {N R : Type*} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  (D : SkewLatticeDatum N) (d : PositiveDegrees D.unfrozen)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "β" => D.coefficientForm R
local notation "hβ" => D.isAlt_coefficientForm R
local notation "𝔤" => SkewLieAlgebra.positiveLieAlgebra β hβ d
local notation "𝓛" => SkewLieAlgebra.positiveGrading β hβ d

/-- Principal coefficient exponents have arbitrary character coordinate and
positive-monoid unfrozen coordinate. -/
def principalCoefficientMonoid : AddSubmonoid Lpr :=
  (⊤ : AddSubmonoid (Module.Dual ℤ D.sublattice)).prod d.monoid

@[simp]
theorem mem_principalCoefficientMonoid (x : Lpr) :
    x ∈ D.principalCoefficientMonoid d ↔ x.2 ∈ d.monoid := by
  simp [principalCoefficientMonoid, AddSubmonoid.mem_prod]

/-- Every principal positive degree is an allowed coefficient exponent. -/
theorem principalPositiveDegrees_le_coefficientMonoid :
    (D.principalPositiveDegrees d).monoid ≤ D.principalCoefficientMonoid d := by
  rintro ⟨m, n⟩ h
  exact (D.mem_principalCoefficientMonoid d _).mpr
    ((PositiveDegrees.mem_graph_monoid d D.principalCharacter.toAddMonoidHom m n).mp h).1

local notation "Qpr" => D.principalCoefficientMonoid d
local notation "Fpr" => TropicalVertexCoefficientAction.filtration
  (R := R) (D.principalPositiveDegrees d) Qpr

/-- The principal skew action on its coefficient monoid algebra, obtained from
the principal logarithmic embedding. -/
def principalCoefficientAction : 𝔤 →ₗ⁅R⁆ Derivation R R[Qpr] R[Qpr] :=
  (tropicalVertexCoefficientAction (D.principalPositiveDegrees d)
    (AddMonoidHom.id Lpr) Qpr (D.principalPositiveDegrees_le_coefficientMonoid d)).comp
      (D.principalGradedLieHom d).toLieHom

/-- The tropical vertex action of a principal image is the principal coefficient action. -/
@[simp]
theorem tropicalVertexCoefficientAction_principalGradedLieHom
    (h : (D.principalPositiveDegrees d).monoid ≤ Qpr) (x : 𝔤) :
    tropicalVertexCoefficientAction (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) Qpr h
      (D.principalGradedLieHom d x) = D.principalCoefficientAction d x := (rfl)

/-- Inclusion in the full group algebra intertwines the principal coefficient
action with the formal principal logarithmic action. -/
theorem mapDomain_principalCoefficientAction (x : 𝔤) (a : R[Qpr]) :
    mapDomainRingHom R (Qpr).subtype (D.principalCoefficientAction d x a) =
      LogarithmicVectorField.action (AddMonoidHom.id Lpr) (D.principalLieHom x.val)
        (mapDomainRingHom R (Qpr).subtype a) := by
  exact (mapDomain_tropicalVertexCoefficientAction _ _ _ _ _ _).trans
    (congrArg (fun z => LogarithmicVectorField.action (AddMonoidHom.id Lpr) z
      (mapDomainRingHom R (Qpr).subtype a)) (D.coe_principalGradedLieHom_apply d x))

omit [CommRing R] [Algebra ℚ R] in
/-- Principal coefficient order is the degree of the retained unfrozen exponent.
Arbitrary Laurent characters contribute order zero. -/
@[simp↓]
theorem mem_principalCoefficientFiltration_ideal_iff [Semiring R] (k : ℕ) (a : R[Qpr]) :
    a ∈ (Fpr).ideal k ↔ ∀ p ∈ a.coeff.support, (k : ℤ) ≤ d.degree p.val.2 := by
  rw [TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.mem_monoidAlgebraIdeal_iff]
  constructor
  · intro ha p hp
    obtain ⟨n, _, hn, q, rfl⟩ := ha p hp
    have he : (D.principalPositiveDegrees d).degree n.val = d.degree n.val.2 :=
      PositiveDegrees.graph_degree d D.principalCharacter.toAddMonoidHom n.val.1 n.val.2
    simp only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply, he] at hn
    have hq := d.degree_nonneg ((D.mem_principalCoefficientMonoid d q.val).mp q.property)
    simpa only [AddSubmonoid.coe_add, Prod.snd_add, map_add] using
      hn.trans (le_add_of_nonneg_left hq)
  · intro ha p hp
    let n : Qpr := ⟨(D.principalCharacter p.val.2, p.val.2),
      (D.mem_principalCoefficientMonoid d _).mpr
        ((D.mem_principalCoefficientMonoid d p.val).mp p.property)⟩
    let q : Qpr := ⟨(p.val.1 - D.principalCharacter p.val.2, 0), by simp⟩
    refine ⟨n, ?_, ?_, q, ?_⟩
    · exact (PositiveDegrees.mem_graph_monoid d D.principalCharacter.toAddMonoidHom _ _).mpr
        ⟨(D.mem_principalCoefficientMonoid d _).mp p.property, rfl⟩
    · simpa only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply, n,
        PositiveDegrees.graph_degree] using ha p hp
    · apply Subtype.ext
      simp [n, q]

omit [CommRing R] [Algebra ℚ R] in
/-- A principal coefficient monomial of nonzero unfrozen degree lies in the first completed
ideal. -/
theorem toCompletion_single_mem_completionIdeal_one {R : Type*} [Ring R] (q : Qpr)
    (hq : q.val.2 ≠ 0) :
    (TropicalVertexCoefficientAction.filtration
        (R := R) (D.principalPositiveDegrees d) Qpr).toCompletion (single q 1) ∈
      (TropicalVertexCoefficientAction.filtration
        (R := R) (D.principalPositiveDegrees d) Qpr).completionIdeal 1 := by
  rw [AlgFiltration.toCompletion_mem_completionIdeal_iff,
    mem_principalCoefficientFiltration_ideal_iff]
  intro p hp
  obtain rfl : p = q := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (by simp [Ne.symm h])
  have := d.degree_pos ((D.mem_principalCoefficientMonoid d _).mp p.property) hq
  omega

omit [CommRing R] [Algebra ℚ R] in
/-- A principal coefficient monomial of nonzero unfrozen degree is congruent to `0`, so
`1 + z^q` is a unit of the principal coefficient completion. -/
theorem exists_units_eq_one_add_single {R : Type*} [Ring R] (q : Qpr) (hq : q.val.2 ≠ 0) :
    ∃ U : (TropicalVertexCoefficientAction.filtration
        (R := R) (D.principalPositiveDegrees d) Qpr).completionˣ,
      (U : (TropicalVertexCoefficientAction.filtration
        (R := R) (D.principalPositiveDegrees d) Qpr).completion) =
      1 + (TropicalVertexCoefficientAction.filtration
        (R := R) (D.principalPositiveDegrees d) Qpr).toCompletion (single q 1) :=
  ⟨(AlgFiltration.isUnit_of_sub_one_mem _ (by
      simpa only [add_sub_cancel_left] using
        D.toCompletion_single_mem_completionIdeal_one (R := R) d q hq)).unit,
    IsUnit.unit_spec _⟩

omit [CommRing R] [Algebra ℚ R] in
/-- The monomial at the principal embedding of a positive degree lies in the first
completed ideal, for any coefficient monoid containing it. -/
theorem toCompletion_single_principalEmbedding_mem_first {R : Type*} [Ring R]
    {n : D.unfrozen} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)
    (P : AddSubmonoid Lpr) (q : P) (hq : q.val = D.principalEmbedding n) :
    (TropicalVertexCoefficientAction.filtration
        (R := R) (D.principalPositiveDegrees d) P).toCompletion (single q 1) ∈
      (TropicalVertexCoefficientAction.filtration
        (R := R) (D.principalPositiveDegrees d) P).completionIdeal 1 := by
  have hpos : (q : Lpr) ∈ (D.principalPositiveDegrees d).monoid := by
    rw [hq, principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
    exact ⟨hn, rfl⟩
  have hdegree : (1 : ℤ) ≤ (D.principalPositiveDegrees d).degree q := by
    rw [hq, principalEmbedding_apply, PositiveDegrees.graph_degree]
    exact d.degree_pos hn hn0
  rw [AlgFiltration.toCompletion_mem_completionIdeal_iff,
    TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  exact Or.inr ⟨q, hpos, hdegree, 0, by simp⟩

/-- Each principal coefficient of the action on a monomial recovers the
corresponding skew coefficient times the principal evaluation character. -/
@[simp]
theorem principalCoefficientAction_coeff (x : 𝔤) (n : d.monoid) (p : Qpr) (c : R) :
    (D.principalCoefficientAction d x (single p c)).coeff
        (⟨(D.principalCharacter n, n), by simp [n.property]⟩ + p) =
      c * (SkewLieAlgebra.toFinsupp β hβ x.val n * D.principalEvaluation n p.val) := by
  classical
  have he := congrArg
    (fun a : R[Lpr] => a.coeff (D.principalEmbedding n + p.val))
    (D.mapDomain_principalCoefficientAction d x (single p c))
  simp only [mapDomainRingHom_apply, mapDomain_single, AddSubmonoid.subtype_apply] at he
  rw [LogarithmicVectorField.action_coeff,
    D.principalLieHom_apply, D.principalEmbedding_apply, D.principalRealization_coeff] at he
  simp only [AddMonoidHom.id_apply, AddMonoidHom.smul_apply, smul_eq_mul] at he
  exact (Finsupp.mapDomain_apply_of_injective (Qpr).subtype_injective
    (D.principalCoefficientAction d x (single p c)).coeff
    (⟨(D.principalCharacter n, n), by simp [n.property]⟩ + p)).symm.trans he

/-- A degree-`n` principal field shifts every coefficient degree by the
principal exponent `(p₁*(n), n)`. -/
theorem principalCoefficientAction_mem_gradeBy {n : D.unfrozen} {p : Lpr}
    {x : 𝔤} {a : R[Qpr]} (hx : x ∈ 𝓛 n) (ha : a ∈ gradeBy R (Qpr).subtype p) :
    D.principalCoefficientAction d x a ∈
      gradeBy R (Qpr).subtype (D.principalEmbedding n + p) := by
  let : Fact ((D.principalPositiveDegrees d).monoid ≤ Qpr) :=
    ⟨D.principalPositiveDegrees_le_coefficientMonoid d⟩
  let := TropicalVertexCoefficientAction.instLieRingModule
    (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) Qpr
  let := TropicalVertexCoefficientAction.instGradedBracket
    (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) Qpr
  have h := SetLike.GradedBracket.bracket_mem ((D.principalGradedLieHom d).map_mem hx) ha
  simpa only [TropicalVertexCoefficientAction.lie_eq, principalCoefficientAction,
    LieHom.comp_apply, PositiveDegrees.graphMap_apply, principalEmbedding_apply,
    LinearMap.toAddMonoidHom_coe, vadd_eq_add] using h

namespace PrincipalCoefficientAction

/-- The principal derivation representation defines the coefficient Lie action. -/
scoped instance instLieRingModule : LieRingModule 𝔤 R[Qpr] :=
  LieRingModule.compLieHom _ (D.principalCoefficientAction d)

/-- The principal coefficient action is linear over its coefficient ring. -/
scoped instance instLieModule : LieModule R 𝔤 R[Qpr] :=
  LieModule.compLieHom _ (D.principalCoefficientAction d)

/-- The selected principal Lie action evaluates its coefficient derivation. -/
@[simp]
theorem lie_eq (x : 𝔤) (a : R[Qpr]) :
    ⁅x, a⁆ = D.principalCoefficientAction d x a := (rfl)

/-- Principal fields act by derivations of coefficient multiplication. -/
scoped instance instIsDerivationAction : IsDerivationAction 𝔤 R[Qpr] where
  lie_mul x a b := by simp [lie_eq, Derivation.leibniz, mul_comm]

/-- The principal action raises coefficient order by the positive Lie degree. -/
scoped instance instIsFiltrationRaising :
    IsFiltrationRaising d 𝓛 ((Fpr).toModuleFiltration R) where
  lie_mem {a b x m} hx hm := by
    let : Fact ((D.principalPositiveDegrees d).monoid ≤ Qpr) :=
      ⟨D.principalPositiveDegrees_le_coefficientMonoid d⟩
    let := TropicalVertexCoefficientAction.instLieRingModule
      (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) Qpr
    let := TropicalVertexCoefficientAction.instIsFiltrationRaising
      (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) Qpr
    have hmap := d.map_degreeSubmodule_le 𝓛
      (d.graphMap D.principalCharacter.toAddMonoidHom)
      (tropicalVertexGrading (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr))
      (D.principalGradedLieHom d).toLieHom.toLinearMap
      (fun _ _ hx => (D.principalGradedLieHom d).map_mem hx) a
    simp only [PositiveDegrees.graphMap_modulus] at hmap
    exact IsFiltrationRaising.lie_mem
      (d := D.principalPositiveDegrees d)
      (ℒ := tropicalVertexGrading (R := R) (D.principalPositiveDegrees d)
        (AddMonoidHom.id Lpr))
      (F := (Fpr).toModuleFiltration R)
      (hmap (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)) hm

variable [Module.Projective ℤ N]

/-- Degree-zero Laurent characters detect every surviving positive skew field,
including fields whose degrees lie in the radical of the skew form. -/
scoped instance instIsFiltrationDetected :
    IsFiltrationDetected d 𝓛 ((Fpr).toModuleFiltration R) where
  exists_lie_not_mem {k x} hx := by
    classical
    -- Read a surviving skew coefficient using the inherited exponent grading.
    have hx' : x.val ∉ d.degreeSubmodule (SkewLieAlgebra.grade β hβ) k := by
      intro h
      apply hx
      rw [d.degreeSubmodule_comap (SkewLieAlgebra.grade β hβ) 𝓛
        (SkewLieAlgebra.positiveLieAlgebra β hβ d).incl.toLinearMap
        Subtype.val_injective (fun _ _ h =>
          (SkewLieAlgebra.mem_positiveGrading_iff β hβ d _ _).mp h)]
      exact h
    rw [d.mem_degreeSubmodule_iff] at hx'
    push Not at hx'
    obtain ⟨n, hnk, hn⟩ := hx'
    have hc : SkewLieAlgebra.toFinsupp β hβ x.val n ≠ 0 := by
      intro h
      rw [SkewLieAlgebra.decompose_grade, h, map_zero] at hn
      exact hn rfl
    have hpos : n ∈ d.monoid ∧ n ≠ 0 := by
      by_contra h
      exact hc ((SkewLieAlgebra.mem_positiveLieAlgebra_iff β hβ d x.val).mp
        x.property n (by tauto))
    -- A dual character nonzero on n has a unit-valued rational evaluation.
    have hnN : (n : N) ≠ 0 := fun h => hpos.2 (Subtype.ext h)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℤ N, φ n ≠ 0 := by
      exact not_forall.mp (mt (Module.forall_dual_apply_eq_zero_iff ℤ (n : N)).mp hnN)
    let p : Qpr := ⟨(φ.comp D.sublattice.subtype, 0), by simp⟩
    let q : Qpr := ⟨(D.principalCharacter n, n), by simp [hpos.1]⟩ + p
    have hu : IsUnit (algebraMap ℚ R (φ n : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hφ)).map (algebraMap ℚ R)
    have hcoeff : (D.principalCoefficientAction d x (single p 1)).coeff q ≠ 0 := by
      rw [D.principalCoefficientAction_coeff d x ⟨n, hpos.1⟩ p 1, one_mul]
      simp only [p, D.principalEvaluation_restrict]
      exact fun h => hc (hu.mul_left_eq_zero.mp h)
    -- The detected output has order at most k, so survives the required cutoff.
    refine ⟨0, single p 1, by simp, ?_⟩
    intro hf
    have hf' : D.principalCoefficientAction d x (single p 1) ∈ (Fpr).ideal (k + 2) := by
      simpa only [AlgFiltration.toModuleFiltration_submodule, Submodule.restrictScalars_mem,
        lie_eq, Nat.zero_add] using hf
    have hd := (D.mem_principalCoefficientFiltration_ideal_iff d (k + 2) _).mp
      hf' q (Finsupp.mem_support_iff.mpr hcoeff)
    simp only [q, p, AddSubmonoid.coe_add, Prod.snd_add, add_zero] at hd
    omega

end PrincipalCoefficientAction

section TropicalComparison

open scoped Mei.TropicalVertexCoefficientAction PrincipalCoefficientAction

variable [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  [Fact ((D.principalPositiveDegrees d).monoid ≤ D.principalCoefficientMonoid d)]

local notation "𝒜" => AlgFiltration.completedBCHAction (Fpr) (D.principalPositiveDegrees d)
    (tropicalVertexGrading (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr))

/-- The integrated principal action of a completed skew group element is the completed
tropical vertex action of its principal image. -/
theorem completedBCHAction_eq_completedMap (g : d.completedBCHGroup 𝓛) :
    (Fpr).completedBCHAction d 𝓛 g = 𝒜 ((D.principalGradedLieHom d).completedMap g) := by
  apply AlgEquiv.ext
  intro z
  have h := (Fpr).mapCompletionₐ_completedBCHAction_of_gradedLieHom (Fpr)
    (D.principalGradedLieHom d) (AlgHom.id R R[Qpr]) (fun _ _ => rfl) id monotone_id
    (fun _ => by simp) g z
  simpa only [AlgFiltration.mapCompletionₐ_id, AlgHom.id_apply] using h

variable [Module.Projective ℤ N] in
/-- Monomials detect the completed skew group: elements whose principal images act
equally on every principal coefficient monomial are equal. -/
theorem eq_of_completedBCHAction_completedMap_single_eq {g h : d.completedBCHGroup 𝓛}
    (hgh : ∀ p : Qpr,
      𝒜 ((D.principalGradedLieHom d).completedMap g) ((Fpr).toCompletion (single p 1)) =
        𝒜 ((D.principalGradedLieHom d).completedMap h) ((Fpr).toCompletion (single p 1))) :
    g = h := by
  have key : ((𝒜 ((D.principalGradedLieHom d).completedMap g)).toAlgHom.comp
        ((Fpr).toCompletionₐ (R := R))) =
      ((𝒜 ((D.principalGradedLieHom d).completedMap h)).toAlgHom.comp
        ((Fpr).toCompletionₐ (R := R))) :=
    AddMonoidAlgebra.algHom_ext (fun p => by simpa using hgh p)
      (Subsingleton.elim _ _)
  refine AlgFiltration.completedBCHAction_injective (Fpr) d 𝓛
    ((D.completedBCHAction_eq_completedMap d g).trans
      (((Fpr).completedBCHAction_eq_of_forall_toCompletion _ _ fun a => ?_).trans
        (D.completedBCHAction_eq_completedMap d h).symm))
  simpa using AlgHom.congr_fun key a

end TropicalComparison

end Mei.SkewLatticeDatum
