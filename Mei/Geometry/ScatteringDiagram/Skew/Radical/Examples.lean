/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Coefficient
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Examples
public import Mei.Geometry.ScatteringDiagram.Skew.Principal.KS.Hyperplane
public import Mei.Geometry.ScatteringDiagram.Skew.Radical
public import Mei.Algebra.PositiveDegrees.Basis

/-!
# Checks on the zero form and on a radical degree

Two checks on skew lattice data whose form is degenerate.

* *The zero form.* For the rank-one datum `Mei.SkewLatticeDatum.Examples.zeroForm` on `ℤ` with the
  zero form, the Poisson action of the skew Lie algebra on `R[N_uf]` is zero
  (`zeroForm_action_eq_zero`), while for every choice of positive degrees the principal action of
  the completed skew group on the completed principal coefficients is faithful
  (`zeroForm_principal_completedBCHAction_injective`).

* *A radical degree.* On `ℤ³` take the form `{x, y} = (x₀ - x₁) y₂ - x₂ (y₀ - y₁)`, with every
  vector unfrozen and `N° = N` (`degenerateRankThree`). It is not zero
  (`degenerateRankThree_form_ne_zero`), and its radical contains the primitive allowed degree
  `n = e₀ + e₁` of `ℕ³` (`form_flip_radicalVector`), although `e₀` is not radical
  (`form_basis_zero_basis_two`).
  - Brackets of total degree `n` vanish: homogeneous elements of degrees `e₀` and `e₁` commute
    (`lie_eq_zero_of_mem_positiveGrading_zero_one`). The generator `X_n` acts by zero in the
    Poisson action (`action_single_radicalVector`).
  - The normal `{-, κ(n) n}` is zero (`normal_radicalVector`), and the skew comparison of the
    standard lattice pulls evaluation at `n` back to zero
    (`eval_comp_skewComparison_radicalVector`).
  - The full KS wall `n⊥` (`radicalWall`, an `IndexedWall.hyperplane`) carries the label
    `exp X_n` of the supported ray of `n`, which is not the identity (`radicalLabel_ne_one`). For
    the KS restriction `ksRestriction`, the identity of `ℝ³`, the KS wall is KS-incoming
    (`radicalWall_ksIncoming`), and its projected principal wall and principal cylinder are
    incoming (`projectedWall_radicalWall_incoming`,
    `cylinder_projectedWall_radicalWall_incoming`).
  - The principal exponent `r(n)` and the principal normal `ν_n` are nonzero
    (`principalEmbedding_radicalVector_ne_zero`, `principalNormal_radicalVector_ne_zero`). The
    projected direction map sends `r(n)` to `0` (`projectedWall_radicalWall_direction`), and the
    principal-cylinder direction map sends it to `r(n)`, so the cylinder moves with the nonzero
    velocity `-r(n)` (`cylinder_projectedWall_radicalWall_direction`,
    `cylinder_projectedWall_radicalWall_direction_ne_zero`).

These checks concern the principal realization of Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1 and Appendix B (arXiv:1411.1394v2).
-/

public section

open TauCeti (AlgFiltration)

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

namespace Mei.SkewLatticeDatum.Examples

open TauCeti.Toric

/-! ### The zero form -/

section ZeroForm

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The Poisson action of the zero-form datum on `ℤ` is zero. -/
theorem zeroForm_action_eq_zero :
    SkewLieAlgebra.action _ (zeroForm.isAlt_coefficientForm R) = 0 :=
  zeroForm.action_eq_zero_of_form_eq_zero R zeroForm_form

open scoped PrincipalCoefficientAction in
/-- For every choice of positive degrees, the principal action of the completed skew group of the
zero-form datum on the completed principal coefficients `R[M°][[t]]` is faithful. -/
theorem zeroForm_principal_completedBCHAction_injective (d : PositiveDegrees zeroForm.unfrozen) :
    Function.Injective
      ((TropicalVertexCoefficientAction.filtration (R := R) (zeroForm.principalPositiveDegrees d)
        (zeroForm.principalCoefficientMonoid d)).completedBCHAction d
        (SkewLieAlgebra.positiveGrading _ (zeroForm.isAlt_coefficientForm R) d)) :=
  AlgFiltration.completedBCHAction_injective _ _ _

end ZeroForm

/-! ### A degenerate form of rank three -/

/-- The skew form `{x, y} = (x₀ - x₁) y₂ - x₂ (y₀ - y₁)` on `ℤ³`. Its radical is spanned by
`e₀ + e₁`. -/
def degenerateForm : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => (((x 0 - x 1) * y 2 - x 2 * (y 0 - y 1) : ℤ) : ℚ))
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- The value of the degenerate form on two vectors of `ℤ³`. -/
@[simp]
theorem degenerateForm_apply (x y : Fin 3 → ℤ) :
    degenerateForm x y = (((x 0 - x 1) * y 2 - x 2 * (y 0 - y 1) : ℤ) : ℚ) :=
  (rfl)

/-- The skew lattice datum on `ℤ³` with the degenerate form `degenerateForm`, every vector
unfrozen and `N° = N`. -/
def degenerateRankThree : SkewLatticeDatum (Fin 3 → ℤ) where
  unfrozen := ⊤
  unfrozen_saturated _ _ _ := Or.inr Submodule.mem_top
  sublattice := ⊤
  finiteIndex_sublattice := by
    simpa only [Submodule.top_toAddSubgroup] using
      (inferInstance : (⊤ : AddSubgroup (Fin 3 → ℤ)).FiniteIndex)
  form := degenerateForm
  isAlt_form x := by simp [mul_comm]
  integral_unfrozen_sublattice a _ b _ := ⟨_, degenerateForm_apply a b⟩
  integral_unfrozen_inf_sublattice a b _ := ⟨_, degenerateForm_apply a b⟩

/-- Every vector of the rank-three datum is unfrozen. -/
@[simp]
theorem degenerateRankThree_unfrozen : degenerateRankThree.unfrozen = ⊤ :=
  (rfl)

/-- The finite-index sublattice of the rank-three datum is all of `ℤ³`. -/
@[simp]
theorem degenerateRankThree_sublattice : degenerateRankThree.sublattice = ⊤ :=
  (rfl)

/-- The form of the rank-three datum is the degenerate form. -/
@[simp]
theorem degenerateRankThree_form : degenerateRankThree.form = degenerateForm :=
  (rfl)

/-- The degenerate form is not zero: `{e₀, e₂} = 1`. -/
theorem degenerateRankThree_form_ne_zero : degenerateRankThree.form ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun₂ h (Pi.single 0 1) (Pi.single 2 1)
  simp at he

/-- The standard basis of the unfrozen lattice `ℤ³`. -/
def rankThreeBasis : Module.Basis (Fin 3) ℤ degenerateRankThree.unfrozen :=
  (Pi.basisFun ℤ (Fin 3)).map (LinearEquiv.ofTop _ degenerateRankThree_unfrozen).symm

/-- The `k`-th vector of the unfrozen basis is the standard basis vector `e_k`. -/
@[simp]
theorem coe_rankThreeBasis (k : Fin 3) : (rankThreeBasis k : Fin 3 → ℤ) = Pi.single k 1 := by
  simp [rankThreeBasis]

/-- The vector `e₀ + e₁`, which spans the radical of the degenerate form. -/
def radicalVector : degenerateRankThree.unfrozen :=
  rankThreeBasis 0 + rankThreeBasis 1

/-- The radical vector is `e₀ + e₁` in `ℤ³`. -/
@[simp]
theorem coe_radicalVector :
    (radicalVector : Fin 3 → ℤ) = Pi.single 0 1 + Pi.single 1 1 := by
  simp [radicalVector]

/-- The vector `e₀ + e₁` lies in the radical of the degenerate form. -/
theorem form_flip_radicalVector : degenerateRankThree.form.flip radicalVector = 0 := by
  ext a
  simp

/-- The basis vector `e₀` does not lie in the radical: `{e₀, e₂} = 1`. -/
theorem form_basis_zero_basis_two :
    degenerateRankThree.form (rankThreeBasis 0) (rankThreeBasis 2) = 1 := by
  simp

/-- The positive degrees `ℕ³` of the unfrozen lattice, with coordinate-sum degree. -/
abbrev rankThreeDegrees : PositiveDegrees degenerateRankThree.unfrozen :=
  rankThreeBasis.positiveDegrees

/-- The radical vector `e₀ + e₁` is an allowed degree. -/
theorem radicalVector_mem_monoid : radicalVector ∈ rankThreeDegrees.monoid := by
  rw [Module.Basis.mem_positiveDegrees_monoid]
  intro j
  fin_cases j <;> simp [radicalVector]

/-- The radical vector `e₀ + e₁` is primitive: its first coordinate is `1`. -/
theorem isPrimitive_radicalVector : TauCeti.IsPrimitive radicalVector :=
  TauCeti.isPrimitive_def.mpr ⟨rankThreeBasis.coord 0, by simp [radicalVector]⟩

/-- The supported ray of the radical vector `e₀ + e₁`. -/
def radicalRay : SupportedRay rankThreeDegrees :=
  SupportedRay.ofMem radicalVector radicalVector_mem_monoid isPrimitive_radicalVector

/-- The generator of the radical ray is `e₀ + e₁`. -/
@[simp]
theorem radicalRay_generator : radicalRay.generator = radicalVector :=
  SupportedRay.generator_ofMem _ _ _

/-- The radical vector is the sum of the first two unfrozen basis vectors. -/
theorem radicalVector_def : radicalVector = rankThreeBasis 0 + rankThreeBasis 1 :=
  (rfl)

/-! #### Brackets, Poisson action and skew comparison at the radical degree -/

section Lie

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- Homogeneous elements of degrees `e₀` and `e₁` commute, since `e₀ + e₁` is radical,
although neither `e₀` nor `e₁` is radical. -/
theorem lie_eq_zero_of_mem_positiveGrading_zero_one
    {x y : SkewLieAlgebra.positiveLieAlgebra (degenerateRankThree.coefficientForm R)
      (degenerateRankThree.isAlt_coefficientForm R) rankThreeDegrees}
    (hx : x ∈ SkewLieAlgebra.positiveGrading _ (degenerateRankThree.isAlt_coefficientForm R)
      rankThreeDegrees (rankThreeBasis 0))
    (hy : y ∈ SkewLieAlgebra.positiveGrading _ (degenerateRankThree.isAlt_coefficientForm R)
      rankThreeDegrees (rankThreeBasis 1)) :
    ⁅x, y⁆ = 0 :=
  degenerateRankThree.lie_eq_zero_of_form_flip_add_eq_zero R rankThreeDegrees
    (by rw [← radicalVector_def]; exact form_flip_radicalVector) hx hy

/-- The generator of the radical degree `e₀ + e₁` acts by zero in the Poisson action. -/
theorem action_single_radicalVector (r : R) :
    SkewLieAlgebra.action _ (degenerateRankThree.isAlt_coefficientForm R)
      (SkewLieAlgebra.single _ (degenerateRankThree.isAlt_coefficientForm R) radicalVector r) =
      0 :=
  degenerateRankThree.action_single_eq_zero_of_form_flip_eq_zero R form_flip_radicalVector r

end Lie

/-- The degenerate form is integral on all of `ℤ³`. -/
theorem degenerateRankThree_integral (a b : Fin 3 → ℤ) :
    ∃ k : ℤ, degenerateRankThree.form a b = k :=
  ⟨_, degenerateForm_apply a b⟩

/-- The normal `{-, κ(n) n}` of the radical vector `n = e₀ + e₁` is zero. -/
theorem normal_radicalVector :
    degenerateRankThree.normal radicalVector radicalVector.property = 0 :=
  (degenerateRankThree.normal_eq_zero_iff _).mpr form_flip_radicalVector

/-- For the standard lattice `ℤ³ ⊆ ℝ³`, the skew comparison `x ↦ {x, -}` pulls evaluation at
the radical vector `e₀ + e₁` back to zero. -/
theorem eval_comp_skewComparison_radicalVector :
    ((ContinuousLinearMap.apply ℝ ℝ
        ((Int.castAddHom ℝ).compLeft (Fin 3) (radicalVector : Fin 3 → ℤ))).toLinearMap).comp
      (degenerateRankThree.skewComparison degenerateRankThree_integral
        (isIntegralLattice_intCast 3)) = 0 :=
  (degenerateRankThree.eval_comp_skewComparison_eq_zero_iff _ _ _).mpr form_flip_radicalVector

/-! #### Lattices and the KS restriction -/

/-- Integral characters of the unfrozen lattice, written by their values on the standard
basis. -/
def characterEquiv : (Fin 3 → ℤ) ≃+ (degenerateRankThree.unfrozen →+ ℤ) :=
  ((rankThreeBasis.constr ℤ).trans (addMonoidHomLequivInt ℤ).symm).toAddEquiv

/-- The character with coordinates `x` takes the value `x k` at `e_k`. -/
@[simp]
theorem characterEquiv_apply_rankThreeBasis (x : Fin 3 → ℤ) (k : Fin 3) :
    characterEquiv x (rankThreeBasis k) = x k := by
  simp [characterEquiv]

/-- The KS lattice `Hom(N_uf, ℤ) → ℝ³`, recording the values of a character on the standard
basis. -/
def ksLattice : (degenerateRankThree.unfrozen →+ ℤ) →+ (Fin 3 → ℝ) :=
  ((Int.castAddHom ℝ).compLeft (Fin 3)).comp characterEquiv.symm.toAddMonoidHom

/-- The `k`-th coordinate of the KS lattice point of a character is its value at `e_k`. -/
@[simp]
theorem ksLattice_apply (f : degenerateRankThree.unfrozen →+ ℤ) (k : Fin 3) :
    ksLattice f k = (f (rankThreeBasis k) : ℝ) := by
  obtain ⟨x, rfl⟩ := characterEquiv.surjective f
  simp [ksLattice]

/-- The KS lattice is an integral lattice in `ℝ³`. -/
theorem isIntegralLattice_ksLattice : IsIntegralLattice ksLattice :=
  (isIntegralLattice_congr characterEquiv (LinearEquiv.refl ℝ _)
    (fun x => by ext k; simp)).mp (isIntegralLattice_intCast 3)

/-- Restriction of integral characters from `N° = ℤ³` to `N_uf = ℤ³`. -/
def restrictEquiv :
    Module.Dual ℤ degenerateRankThree.sublattice ≃+ (degenerateRankThree.unfrozen →+ ℤ) :=
  ((LinearEquiv.ofEq _ _ (by simp)).dualMap.trans (addMonoidHomLequivInt ℤ).symm).toAddEquiv

/-- Restriction evaluates a character of `N°` at the same vector of `N_uf`. -/
@[simp]
theorem restrictEquiv_apply (m : Module.Dual ℤ degenerateRankThree.sublattice)
    (n : degenerateRankThree.unfrozen) :
    restrictEquiv m n = m ⟨n, by simp⟩ :=
  (rfl)

/-- The lattice `M° → ℝ³` of characters of `N°`, through their restrictions to `N_uf`. -/
def characterLattice : Module.Dual ℤ degenerateRankThree.sublattice →+ (Fin 3 → ℝ) :=
  ksLattice.comp restrictEquiv.toAddMonoidHom

/-- The character lattice point of `m` is the KS lattice point of its restriction. -/
@[simp]
theorem characterLattice_apply (m : Module.Dual ℤ degenerateRankThree.sublattice) :
    characterLattice m = ksLattice (restrictEquiv m) :=
  (rfl)

/-- The character lattice `M° → ℝ³` is an integral lattice. -/
theorem isIntegralLattice_characterLattice : IsIntegralLattice characterLattice :=
  (isIntegralLattice_congr restrictEquiv (LinearEquiv.refl ℝ _)
    (fun m => by simp)).mpr isIntegralLattice_ksLattice

/-- The unfrozen lattice is free, with basis `rankThreeBasis`. -/
instance : Module.Free ℤ degenerateRankThree.unfrozen :=
  Module.Free.of_basis rankThreeBasis

/-- The unfrozen lattice is finitely generated, by `rankThreeBasis`. -/
instance : Module.Finite ℤ degenerateRankThree.unfrozen :=
  Module.Finite.of_basis rankThreeBasis

/-- The KS space `ℝ³ = Hom(N_uf, ℝ)` of the unfrozen lattice. -/
def ksSpace : KSSpace isIntegralLattice_ksLattice :=
  KSSpace.ofLattice isIntegralLattice_ksLattice

/-- Evaluation in the KS space is the real extension of evaluation of characters. -/
@[simp]
theorem ksSpace_evaluation (θ : Fin 3 → ℝ) (n : degenerateRankThree.unfrozen) :
    ksSpace.evaluation θ n = isIntegralLattice_ksLattice.realCharacter (AddMonoidHom.eval n) θ :=
  KSSpace.ofLattice_evaluation _ θ n

/-- With `N° = N_uf = ℤ³`, the identity of `ℝ³` restricts characters. -/
def ksRestriction : degenerateRankThree.KSRestriction isIntegralLattice_characterLattice ksSpace
    where
  toLinearMap := LinearMap.id
  surjective := Function.surjective_id
  evaluation_apply m n hn := by
    simp

/-- The KS restriction of the rank-three datum is the identity of `ℝ³`. -/
@[simp]
theorem ksRestriction_toLinearMap : ksRestriction.toLinearMap = LinearMap.id :=
  (rfl)

/-- The lattice `N_uf = ℤ³ ⊆ ℝ³` of the principal cylinders. -/
def unfrozenLattice : degenerateRankThree.unfrozen →+ (Fin 3 → ℝ) :=
  ((Int.castAddHom ℝ).compLeft (Fin 3)).comp rankThreeBasis.equivFun.toAddMonoidHom

/-- The cylinder lattice records the standard coordinates of an unfrozen vector. -/
@[simp]
theorem unfrozenLattice_apply (n : degenerateRankThree.unfrozen) :
    unfrozenLattice n = (Int.castAddHom ℝ).compLeft (Fin 3) (rankThreeBasis.equivFun n) :=
  (rfl)

/-- The cylinder lattice `N_uf → ℝ³` is an integral lattice. -/
theorem isIntegralLattice_unfrozenLattice : IsIntegralLattice unfrozenLattice :=
  (isIntegralLattice_congr rankThreeBasis.equivFun.toAddEquiv (LinearEquiv.refl ℝ _)
    (fun n => unfrozenLattice_apply n)).mpr (isIntegralLattice_intCast 3)

/-! #### The full KS wall of the radical degree -/

section Wall

/-- Equality of integral characters of `N°`, chosen classically, as required to compare degrees
of principal walls. -/
noncomputable local instance : DecidableEq (Module.Dual ℤ degenerateRankThree.sublattice) :=
  Classical.decEq _

variable (R : Type*) [CommRing R] [Algebra ℚ R]

local notation "𝓛₃" => SkewLieAlgebra.positiveGrading (degenerateRankThree.coefficientForm R)
  (degenerateRankThree.isAlt_coefficientForm R) rankThreeDegrees

/-- The generator `X_(e₀+e₁)` of the radical degree in the positive skew Lie algebra. -/
def radicalGenerator : SkewLieAlgebra.positiveLieAlgebra (degenerateRankThree.coefficientForm R)
    (degenerateRankThree.isAlt_coefficientForm R) rankThreeDegrees :=
  ⟨SkewLieAlgebra.single _ _ radicalVector 1, by
    rw [SkewLieAlgebra.mem_positiveLieAlgebra_iff]
    rintro n hn
    rw [SkewLieAlgebra.toFinsupp_single]
    refine Finsupp.single_eq_of_ne ?_
    rintro rfl
    rcases hn with hn | hn
    · exact hn radicalVector_mem_monoid
    · exact isPrimitive_radicalVector.ne_zero hn⟩

/-- The radical generator is the skew generator `X_(e₀+e₁)` with coefficient `1`. -/
@[simp]
theorem coe_radicalGenerator :
    (radicalGenerator R : SkewLieAlgebra (degenerateRankThree.coefficientForm R)
      (degenerateRankThree.isAlt_coefficientForm R)) =
      SkewLieAlgebra.single _ _ radicalVector 1 :=
  (rfl)

/-- The radical generator is homogeneous of degree `e₀ + e₁`. -/
theorem radicalGenerator_mem : radicalGenerator R ∈ 𝓛₃ radicalVector :=
  (SkewLieAlgebra.mem_positiveGrading_iff _ _ _ _ _).mpr
    ((SkewLieAlgebra.mem_grade_iff _ _ _ _).mpr ⟨1, (coe_radicalGenerator R).symm⟩)

/-- The completed exponential of `X_(e₀+e₁)`, a label in the group of the radical ray. -/
def radicalLabel : rankThreeDegrees.completedBCHGroup 𝓛₃ :=
  rankThreeDegrees.expToCompletion 𝓛₃ (radicalGenerator R)

/-- The radical label is the completed exponential of the radical generator. -/
@[simp]
theorem radicalLabel_def :
    radicalLabel R = rankThreeDegrees.expToCompletion 𝓛₃ (radicalGenerator R) :=
  (rfl)

/-- The radical label lies in the completed group of the radical ray. -/
theorem radicalLabel_mem :
    radicalLabel R ∈ rankThreeDegrees.completedRaySubgroup 𝓛₃ radicalRay := by
  rw [radicalLabel_def]
  refine rankThreeDegrees.expToCompletion_mem_completedRaySubgroup 𝓛₃
    (le_rayLieSubalgebra 𝓛₃ ?_ (radicalGenerator_mem R))
  rw [← radicalRay_generator, SupportedRay.generator_mem_rayDegrees_iff, radicalRay_generator]
  exact radicalVector_mem_monoid

/-- Over a nontrivial ring the radical label is not the identity: it survives at order two. -/
theorem radicalLabel_ne_one [Nontrivial R] : radicalLabel R ≠ 1 := by
  intro h
  have hp := congrArg (TauCeti.CompletedGroup.projection 2) h
  rw [map_one, radicalLabel_def] at hp
  rcases (PositiveDegrees.projection_expToCompletion_eq_one_iff _ _
    (radicalGenerator_mem R) 2).mp hp with hp | hp
  · have hv := congrArg Subtype.val hp
    simp [radicalGenerator] at hv
  · simp [radicalVector, Fin.sum_univ_three] at hp

/-- The full KS hyperplane `(e₀ + e₁)⊥` of the radical ray, with the label `exp X_(e₀+e₁)`. -/
def radicalWall : IndexedWall ksSpace rankThreeDegrees 𝓛₃ :=
  IndexedWall.hyperplane ksSpace radicalRay (radicalLabel R) (radicalLabel_mem R)

/-- The radical wall lies on the radical ray. -/
@[simp]
theorem radicalWall_ray : (radicalWall R).ray = radicalRay :=
  IndexedWall.hyperplane_ray _ _ _ _

/-- The support of the radical wall is the KS hyperplane `(e₀ + e₁)⊥`. -/
@[simp]
theorem radicalWall_support :
    (radicalWall R).support = LinearMap.ker (ksSpace.normal radicalVector) := by
  rw [radicalWall, IndexedWall.hyperplane_support, radicalRay_generator]

/-- The radical wall carries the radical label. -/
@[simp]
theorem radicalWall_label : (radicalWall R).label = radicalLabel R :=
  IndexedWall.hyperplane_label _ _ _ _

/-- The radical wall is KS-incoming: its support contains the restriction of `p₁*(e₀ + e₁)`. -/
theorem radicalWall_ksIncoming :
    ksRestriction.toLinearMap
        (characterLattice (degenerateRankThree.principalCharacter radicalVector)) ∈
      (radicalWall R).support := by
  rw [radicalWall_support]
  exact ksRestriction.apply_principalCharacter_mem_ker_normal radicalVector

/-- The projected principal wall of the radical wall is incoming. -/
theorem projectedWall_radicalWall_incoming :
    (ksRestriction.projectedWall (radicalWall R)).Incoming :=
  ksRestriction.projectedWall_hyperplane_incoming _ _ _

/-- The principal cylinder of the radical wall is incoming. -/
theorem cylinder_projectedWall_radicalWall_incoming :
    ((ksRestriction.projectedWall (radicalWall R)).cylinder
      isIntegralLattice_unfrozenLattice).Incoming :=
  ksRestriction.cylinder_projectedWall_hyperplane_incoming _ _ _ _

/-- The principal exponent `r(e₀ + e₁) = (0, e₀ + e₁)` is nonzero. -/
theorem principalEmbedding_radicalVector_ne_zero :
    degenerateRankThree.principalEmbedding radicalVector ≠ 0 := fun h =>
  isPrimitive_radicalVector.ne_zero (degenerateRankThree.principalEmbedding_injective
    (h.trans (map_zero _).symm))

/-- The principal normal `ν_(e₀+e₁)` is nonzero. -/
theorem principalNormal_radicalVector_ne_zero :
    degenerateRankThree.principalNormal radicalVector ≠ 0 :=
  (degenerateRankThree.principalNormal_eq_zero_iff _).not.mpr isPrimitive_radicalVector.ne_zero

/-- The projected direction map sends `r(e₀ + e₁)` to `0`: the projected principal wall of the
radical wall has zero spatial velocity. -/
theorem projectedWall_radicalWall_direction :
    (ksRestriction.projectedWall (radicalWall R)).direction = 0 :=
  projectedPrincipal_direction_eq_zero_of_form_flip_eq_zero _
    (ksRestriction.projectedWall_ray_generator _)
    (by rw [radicalWall_ray, radicalRay_generator]; exact form_flip_radicalVector)

/-- The principal-cylinder direction map sends `r(e₀ + e₁)` to itself: the principal cylinder
of the radical wall moves with the nonzero velocity `-r(e₀ + e₁)`. -/
theorem cylinder_projectedWall_radicalWall_direction :
    ((ksRestriction.projectedWall (radicalWall R)).cylinder
      isIntegralLattice_unfrozenLattice).direction =
      -(characterLattice.prodMap unfrozenLattice)
        (degenerateRankThree.principalEmbedding radicalVector) := by
  rw [principalCylinder_direction_eq _ _ (ksRestriction.projectedWall_ray_generator _),
    radicalWall_ray, radicalRay_generator]

/-- The principal cylinder of the radical wall has the nonzero velocity `-r(e₀ + e₁)`. -/
theorem cylinder_projectedWall_radicalWall_direction_ne_zero :
    ((ksRestriction.projectedWall (radicalWall R)).cylinder
      isIntegralLattice_unfrozenLattice).direction ≠ 0 := by
  rw [cylinder_projectedWall_radicalWall_direction, neg_ne_zero]
  intro h
  exact principalEmbedding_radicalVector_ne_zero
    ((isIntegralLattice_characterLattice.prod isIntegralLattice_unfrozenLattice).injective
      (h.trans (map_zero _).symm))

end Wall

end Mei.SkewLatticeDatum.Examples
