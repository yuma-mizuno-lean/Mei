/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Coefficient

/-!
# Principal actions of the BLM extension

The BLM extension's spatial lattice identifies with the original principal lattice.
Transporting cylinder normals by the inverse identification gives a tropical pairing
on their span. The pairing preserves evaluations on every coefficient exponent,
including Laurent characters, and sends each initial normal to the original
primitive principal normal. No nondegeneracy of the skew form is required.

Weighting by the independent polynomial variables gives a graded Lie map. The
existing principal coefficient substitution intertwines its Lie actions and,
over a rational algebra, its completed BCH actions on arbitrary completed
coefficients. Thus the substitution compares wall actions as well as functions.

We reuse `principalBLMSpaceEquiv`, `BLMPolynomialInput.alphabetNormalSpan`,
`TropicalPairing.coefficientGradedLieHom`, and
`AlgFiltration.mapCompletionₐ_completedBCHAction_of_gradedLieHom`. The extension
comparison parallels `BLMPolynomialInput.principalCoefficientGradedLieHom`
and follows Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §9.2 (arXiv:2503.03719v1). Principal normals use the conventions of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open Module LogarithmicVectorField _root_.AddMonoidAlgebra

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N}
  (B : D.AdaptedBasis ι) [DecidableEq ι] [Fintype ι] [Nonempty ι]
  (ℓ : B.unfrozenIndex → ℕ+)

local notation "I" => B.principalBLMExtension ℓ
local notation "E" => BLMPolynomialInput.Letter I
local notation "Γ" => Module.Dual ℤ ((ι ⊕ B.unfrozenIndex) →₀ ℤ) × (E → ℤ)
local notation "𝕃" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "𝒅" => PositiveDegrees.finiteAlphabet (BLMPolynomialInput.letterExponent I)
local notation "𝒆" => D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees
local notation "𝒫" => B.principalBLMExtensionCoefficientMonoid ℓ
local notation "𝒬" => D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees
local notation "ϱ" => AddMonoidHom.id Γ
local notation "ϱ'" => AddMonoidHom.id 𝕃

variable (R : Type*) [CommRing R]

/-- Identify the extension's cylinder characters with characters of the original
principal lattice. The degree map retains its identity cutoff modulus. -/
def principalBLMExtensionTropicalPairing :
    TropicalPairing (d := 𝒅) (e := 𝒆) (ρ := ϱ) (ρ' := ϱ')
      ((B.principalBLMExtension ℓ).alphabetNormalSpan R) where
  degreeMap := B.principalBLMExtensionDegreeMap ℓ
  characterMap :=
    { toFun m := m.val.comp ((AddMonoidHom.inl _ _).comp
        B.principalBLMSpaceEquiv.symm.toAddMonoidHom)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  eval_eq m n _ := by
    simpa [principalBLMExtensionDegreeMap_apply, principalBLMExtensionLift_apply] using
      ((B.principalBLMExtension ℓ).alphabetNormalSpan_apply R m n).symm

@[simp]
theorem principalBLMExtensionTropicalPairing_degreeMap :
    (B.principalBLMExtensionTropicalPairing ℓ R).degreeMap =
      B.principalBLMExtensionDegreeMap ℓ := (rfl)

/-- The transported character evaluates on the inverse spatial identification,
with zero independent-letter coordinates. -/
@[simp]
theorem principalBLMExtensionTropicalPairing_characterMap_apply
    (m : (B.principalBLMExtension ℓ).alphabetNormalSpan R) (q : 𝕃) :
    (B.principalBLMExtensionTropicalPairing ℓ R).characterMap m q =
      m.val (B.principalBLMSpaceEquiv.symm q, 0) := (rfl)

/-- The normal pairing holds on the whole coefficient lattice, rather than only
on positive increments. -/
@[simp↓]
theorem principalBLMExtensionTropicalPairing_eval
    (m : (B.principalBLMExtension ℓ).alphabetNormalSpan R) (q : Γ) :
    (B.principalBLMExtensionTropicalPairing ℓ R).characterMap m
        (B.principalBLMExtensionLift ℓ q) = m.val q := by
  rw [principalBLMExtensionTropicalPairing_characterMap_apply,
    principalBLMExtensionLift_apply, LinearEquiv.symm_apply_apply]
  exact (B.principalBLMExtension ℓ).alphabetNormalSpan_apply R m q |>.symm

/-- An initial extension normal becomes exactly the primitive principal normal
of the corresponding original unfrozen basis vector. -/
@[simp]
theorem principalBLMExtensionTropicalPairing_alphabetNormal [Module.Free ℤ N]
    (i : B.unfrozenIndex) :
    (B.principalBLMExtensionTropicalPairing ℓ R).characterMap
        ⟨(Int.castAddHom R).comp ((B.principalBLMExtension ℓ).alphabetNormal
          (B.principalBLMUnfrozenEquiv ℓ i)),
          (B.principalBLMExtension ℓ).alphabetNormal_mem_span R _⟩ =
      (Int.castAddHom R).comp (D.principalNormal (B.unfrozenBasis i)).toAddMonoidHom := by
  ext q
  rw [principalBLMExtensionTropicalPairing_characterMap_apply]
  simp only [AddMonoidHom.comp_apply, BLMPolynomialInput.alphabetNormal_apply,
    principalBLMBasis_basis, coe_principalBLMUnfrozenEquiv,
    Finsupp.coe_basisSingleOne]
  have h := B.principalNormal_principalBLMSpaceEquiv i (B.principalBLMSpaceEquiv.symm q)
  rw [LinearEquiv.apply_symm_apply] at h
  have hi : B.unfrozenBasis i = ⟨B.basis i, B.basis_mem_unfrozen i⟩ :=
    Subtype.ext (B.coe_unfrozenBasis i)
  rw [hi]
  exact congrArg (Int.castAddHom R) h.symm

local notation "𝒮" => MvPolynomial E R
local notation "𝒰" => BLMPolynomialInput.alphabetNormalSpan I R
local notation "χ" => B.principalBLMExtensionCoefficientWeight ℓ R

/-- The weighted graded Lie map from the extension to the original principal
realization. Independent polynomial weights are retained before degrees merge. -/
def principalBLMExtensionCoefficientGradedLieHom :
    GradedLieHom (R := R) (L := tropicalSubalgebra ϱ 𝒰 𝒅)
      (L' := tropicalVertexLieAlgebra (R := 𝒮) 𝒆 ϱ')
      (B.principalBLMExtensionDegreeMap ℓ) (tropicalSubalgebraGrading ϱ 𝒰 𝒅)
      (fun n => Submodule.restrictScalars R (tropicalVertexGrading (R := 𝒮) 𝒆 ϱ' n)) where
  toLieHom := ((B.principalBLMExtensionTropicalPairing ℓ 𝒮).coefficientGradedLieHom
    (U := 𝒰) (Algebra.ofId R 𝒮) χ
    (B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ)
    ((B.principalBLMExtension ℓ).comp_mem_alphabetNormalSpan R (algebraMap R 𝒮))).toLieHom
  map_mem hx := by
    simpa only [principalBLMExtensionTropicalPairing_degreeMap,
      Submodule.restrictScalars_mem] using
      ((B.principalBLMExtensionTropicalPairing ℓ 𝒮).coefficientGradedLieHom
        (U := 𝒰) (Algebra.ofId R 𝒮) χ
        (B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ)
        ((B.principalBLMExtension ℓ).comp_mem_alphabetNormalSpan R (algebraMap R 𝒮))).map_mem hx

/-- A tangent generator acquires its source polynomial weight, transported
principal degree, and transported cylinder character. -/
@[simp]
theorem coe_principalBLMExtensionCoefficientGradedLieHom_tropicalSingle
    {n : Γ} (hn : n ∈ (𝒅).monoid) (hne : n ≠ 0)
    (m : 𝒰) (hm : m.val n = 0) :
    (B.principalBLMExtensionCoefficientGradedLieHom ℓ R
        (tropicalSingle 𝒅 ϱ 𝒰 hn hne m hm)).val =
      LogarithmicVectorField.single ϱ' (B.principalBLMExtensionLift ℓ n)
        (χ (.ofAdd ⟨n, B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ hn⟩) •
          (B.principalBLMExtensionTropicalPairing ℓ 𝒮).characterMap
            ⟨((Algebra.ofId R 𝒮 : R →ₐ[R] 𝒮) : R →+ 𝒮).comp m.val,
              (B.principalBLMExtension ℓ).comp_mem_alphabetNormalSpan R (algebraMap R 𝒮) m⟩) := by
  simpa only [← GradedLieHom.coe_toLieHom, principalBLMExtensionCoefficientGradedLieHom,
    principalBLMExtensionTropicalPairing_degreeMap, principalBLMExtensionDegreeMap_apply] using
    (B.principalBLMExtensionTropicalPairing ℓ 𝒮).coe_coefficientGradedLieHom_tropicalSingle
      (Algebra.ofId R 𝒮) χ (B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ)
      ((B.principalBLMExtension ℓ).comp_mem_alphabetNormalSpan R (algebraMap R 𝒮)) hn hne m hm

private theorem principalBLMExtensionCoefficientMap_eq_comp
    (hQ : (𝒫).map (B.principalBLMExtensionTropicalPairing ℓ 𝒮).degreeMap.toAddMonoidHom ≤ 𝒬) :
    B.principalBLMExtensionCoefficientMap ℓ R =
      (AlgHom.restrictScalars R (mapDomainAlgHom 𝒮 𝒮
        ((AddSubmonoid.inclusion hQ).comp
          ((B.principalBLMExtensionTropicalPairing ℓ 𝒮).degreeMap.toAddMonoidHom.addSubmonoidMap
            𝒫)))).comp (AddMonoidAlgebra.coefficientTwist R χ) := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro q
  simp only [principalBLMExtensionCoefficientMap_single, AlgHom.comp_apply,
    AddMonoidAlgebra.coefficientTwist_single, AlgHom.restrictScalars_apply,
    mapDomainAlgHom_apply, mapDomain_single, principalBLMExtensionCoefficientWeight_apply]
  congr 1
  apply Subtype.ext
  simp only [coe_principalBLMExtensionCoefficientExponent, AddMonoidHom.comp_apply,
    AddSubmonoid.coe_inclusion, AddMonoidHom.addSubmonoidMap_apply_coe,
    principalBLMExtensionTropicalPairing_degreeMap, principalBLMExtensionDegreeMap_apply,
    principalBLMExtensionLift_apply]

/-- The principal substitution intertwines the Lie actions on the original
coefficient monoid algebras, including Laurent spatial coefficients. -/
theorem principalBLMExtensionCoefficientMap_coefficientAction
    (x : tropicalSubalgebra ϱ 𝒰 𝒅) (a : R[𝒫]) :
    B.principalBLMExtensionCoefficientMap ℓ R
        (tropicalVertexCoefficientAction 𝒅 ϱ 𝒫
          (B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ) x.val a) =
      tropicalVertexCoefficientAction 𝒆 ϱ' 𝒬
        (D.principalPositiveDegrees_le_coefficientMonoid B.unfrozenBasis.positiveDegrees)
        (B.principalBLMExtensionCoefficientGradedLieHom ℓ R x)
        (B.principalBLMExtensionCoefficientMap ℓ R a) := by
  have hQ : (𝒫).map
      (B.principalBLMExtensionTropicalPairing ℓ 𝒮).degreeMap.toAddMonoidHom ≤ 𝒬 := by
    simpa only [principalBLMExtensionTropicalPairing_degreeMap] using
      B.map_principalBLMExtensionCoefficientMonoid_le ℓ
  have h := (B.principalBLMExtensionTropicalPairing ℓ 𝒮).map_coefficientAction
    (U := 𝒰) (Q := 𝒫) (Q' := 𝒬) (Algebra.ofId R 𝒮) χ
    (B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ)
    ((B.principalBLMExtension ℓ).comp_mem_alphabetNormalSpan R (algebraMap R 𝒮))
    (D.principalPositiveDegrees_le_coefficientMonoid B.unfrozenBasis.positiveDegrees) hQ
    (AddMonoidAlgebra.coefficientTwist R χ)
    (AddMonoidAlgebra.coefficientTwist_single R χ)
    (fun m q _ => by
      simpa only [principalBLMExtensionTropicalPairing_degreeMap,
        principalBLMExtensionDegreeMap_apply, AddMonoidHom.id_apply] using
        B.principalBLMExtensionTropicalPairing_eval ℓ 𝒮 m q) x a
  simpa only [← B.principalBLMExtensionCoefficientMap_eq_comp ℓ R hQ,
    ← GradedLieHom.coe_toLieHom, principalBLMExtensionCoefficientGradedLieHom] using h

end Mei.SkewLatticeDatum.AdaptedBasis

namespace Mei.SkewLatticeDatum.AdaptedBasis

universe u

open LogarithmicVectorField _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

variable {N ι : Type u} [AddCommGroup N] {D : SkewLatticeDatum N}
  (B : D.AdaptedBasis ι) [DecidableEq ι] [Fintype ι] [Nonempty ι]
  (ℓ : B.unfrozenIndex → ℕ+) (R : Type*) [CommRing R] [Algebra ℚ R]

local notation "I" => B.principalBLMExtension ℓ
local notation "E" => BLMPolynomialInput.Letter I
local notation "Γ" => Module.Dual ℤ ((ι ⊕ B.unfrozenIndex) →₀ ℤ) × (E → ℤ)
local notation "𝕃" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "𝒅" => PositiveDegrees.finiteAlphabet (BLMPolynomialInput.letterExponent I)
local notation "𝒆" => D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees
local notation "𝒫" => B.principalBLMExtensionCoefficientMonoid ℓ
local notation "𝒬" => D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees
local notation "𝒮" => MvPolynomial E R
local notation "ϱ" => AddMonoidHom.id Γ
local notation "ϱ'" => AddMonoidHom.id 𝕃
local notation "𝓛" => tropicalSubalgebraGrading ϱ (BLMPolynomialInput.alphabetNormalSpan I R) 𝒅
local notation "𝓛'" => (fun n =>
  Submodule.restrictScalars R (tropicalVertexGrading (R := 𝒮) 𝒆 ϱ' n))
local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 𝒫
local notation "G" => TropicalVertexCoefficientAction.filtration (R := 𝒮) 𝒆 𝒬

variable [DecidableEq N] [DecidableEq (Module.Dual ℤ ((ι ⊕ B.unfrozenIndex) →₀ ℤ))]
  [DecidableEq (Module.Dual ℤ D.sublattice)]

local instance : Fact ((𝒅).monoid ≤ 𝒫) :=
  ⟨B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ⟩

local instance : Fact ((𝒆).monoid ≤ 𝒬) :=
  ⟨D.principalPositiveDegrees_le_coefficientMonoid B.unfrozenBasis.positiveDegrees⟩

local instance : LieModule R (tropicalVertexLieAlgebra (R := 𝒮) 𝒆 ϱ') 𝒮[𝒬] :=
  LieModule.restrictScalars R 𝒮 _ _

local instance : IsFiltrationRaising 𝒆 𝓛' ((G).toModuleFiltration R) :=
  IsFiltrationRaising.restrictScalars_algebra (R := R) (S := 𝒮) (G) 𝒆
    (tropicalVertexGrading (R := 𝒮) 𝒆 ϱ')

/-- The completed extension substitution intertwines arbitrary completed BCH
labels and completed coefficients in the original principal realization. -/
theorem principalBLMExtensionCompletionMap_completedBCHAction
    (g : (𝒅).completedBCHGroup 𝓛) (a : (F).completion) :
    B.principalBLMExtensionCompletionMap ℓ
        ((F).completedBCHAction 𝒅 𝓛 g a) =
      (G).completedBCHAction (R := R) 𝒆 𝓛'
        ((B.principalBLMExtensionCoefficientGradedLieHom ℓ R).completedMap g)
        (B.principalBLMExtensionCompletionMap ℓ a) := by
  simp only [B.principalBLMExtensionCompletionMap_def ℓ (R := R)]
  exact (F).mapCompletionₐ_completedBCHAction_of_gradedLieHom G
    (B.principalBLMExtensionCoefficientGradedLieHom ℓ R)
    (B.principalBLMExtensionCoefficientMap ℓ R)
    (fun x b => B.principalBLMExtensionCoefficientMap_coefficientAction ℓ R x b)
    id monotone_id (B.filtration_ideal_le_comap_principalBLMExtensionCoefficientMap ℓ R) g a

end Mei.SkewLatticeDatum.AdaptedBasis
