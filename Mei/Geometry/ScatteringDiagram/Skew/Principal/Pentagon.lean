/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Halfspace
public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Positive
public import Mei.Geometry.ScatteringDiagram.Skew.Pentagon
import Mei.Algebra.MonoidAlgebra.Filtration.PowerSeries

/-!
# The cluster scattering pentagon diagram with isolated indices and coefficients

An adapted basis of a skew lattice datum is *of type `A₂` with isolated indices* at two unfrozen
indices `i₁, i₂` (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂WithIsolated`) when
`{e_{i₁}, e_{i₂}} = 1`, every unfrozen multiplier is one, and every other unfrozen basis vector
pairs to zero with all unfrozen basis vectors; frozen indices are allowed. Without other unfrozen
indices the form on `N_uf` is of type `A₂`; with them it is degenerate. Write `ν₁, ν₂` for the
principal normals of `e_{i₁}, e_{i₂}` on the principal lattice `L_pr = M° × N_uf`. For
coefficients `aᵢ` in a commutative `ℚ`-algebra `R`, the adapted polynomial input with `ℓᵢ = 1` has
the full hyperplanes `{νᵢ = 0}` and wall functions `1 + aᵢ q^{eᵢ}` at all unfrozen indices `i`;
for `a = 1` it is the ordinary binomial input.

* Adding the half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}`, cooriented by `ν₁ + ν₂` and labelled by the
  principal image of the ray label of `-Li₂(-a_{i₁} a_{i₂} T)` at `e_{i₁} + e_{i₂}`
  (`IsTypeA₂WithIsolated.outgoingWall`), gives a consistent diagram, the *pentagon diagram*
  (`IsTypeA₂WithIsolated.pentagonDiagram_consistent`), whose new wall is outgoing. It is
  therefore an outgoing completion of the input
  (`IsTypeA₂WithIsolated.isOutgoingCompletion_pentagonDiagram`) and represents its scattering
  class (`IsTypeA₂WithIsolated.scat_eq_toClass_pentagonDiagram`).
* Each wall of this diagram, at the degree `n` among the `eᵢ` and `e_{i₁} + e_{i₂}`
  (`SkewLatticeDatum.AdaptedBasis.pentagonDegree`) with the coefficient `c` among the `aᵢ` and
  `a_{i₁} a_{i₂}` (`SkewLatticeDatum.AdaptedBasis.pentagonCoefficient`), has the wall function
  `1 + c q^n = 1 + c z^{r(n)}` for its principal normal, if the coefficient monoid `Q` contains
  every character `(χ, 0)` (`IsTypeA₂WithIsolated.isWallFunction_discrete_pentagonDiagram`). If
  the `aᵢ` lie in the image of a semiring map `φ : S →+* R`, the discrete grouping is positive for
  the image of `S[Q]`, so the diagram is a positive wall representative of the scattering class
  (`IsTypeA₂WithIsolated.exists_isPositiveWallRepresentative_scat`). For independent variables
  `aᵢ` over `ℚ` the grouped wall functions have coefficients in `ℕ[aᵢ]`; for `a = 1` they are
  `1 + q^n` with natural-number coefficients.

The walls at `i₁`, `i₂` and the outgoing wall are in pentagon configuration
(`IsTypeA₂WithIsolated.isPentagonConfiguration`), and their labels satisfy the pentagon identity
with coefficients (`IsTypeA₂WithIsolated.pentagonDiagram_label_pentagon`). The labels at the
isolated indices commute with all labels of the diagram
(`IsTypeA₂WithIsolated.commute_pentagonDiagram_label`). Instances are in
`Mei.Geometry.ScatteringDiagram.Skew.Principal.Examples`.

These are the positivity statements of Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 and Theorem 1.13 (arXiv:1411.1394v2), for the exchange matrices of type
`A₂` with isolated vertices, with the coefficients of the principal realization (§1 and Appendix B
there). The relation between the walls at `i₁`, `i₂` is the pentagon identity of Nakanishi,
*Cluster algebras and scattering diagrams, Part III*, §5 (arXiv:2111.00800v6).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open _root_.AddMonoidAlgebra PowerSeries
open scoped Mei.TropicalVertexCoefficientAction

variable {N R ι V M : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} (B : D.AdaptedBasis ι)

/-- The degrees of the walls of the pentagon diagram at the unfrozen indices `i₁, i₂`: the
basis vector `eᵢ` for the input wall at `i`, and `e_{i₁} + e_{i₂}` for the outgoing wall. -/
def pentagonDegree (i₁ i₂ : B.unfrozenIndex) : B.unfrozenIndex ⊕ Unit → D.unfrozen :=
  Sum.elim B.unfrozenBasis fun _ => B.unfrozenBasis i₁ + B.unfrozenBasis i₂

/-- The degree of the input wall at `i` is `eᵢ`. -/
@[simp]
theorem pentagonDegree_inl (i₁ i₂ i : B.unfrozenIndex) :
    B.pentagonDegree i₁ i₂ (.inl i) = B.unfrozenBasis i := (rfl)

/-- The degree of the outgoing wall is `e_{i₁} + e_{i₂}`. -/
@[simp]
theorem pentagonDegree_inr (i₁ i₂ : B.unfrozenIndex) (u : Unit) :
    B.pentagonDegree i₁ i₂ (.inr u) = B.unfrozenBasis i₁ + B.unfrozenBasis i₂ := (rfl)

/-- The degrees of the walls are allowed degrees. -/
theorem pentagonDegree_mem_positiveDegrees_monoid (i₁ i₂ : B.unfrozenIndex)
    (j : B.unfrozenIndex ⊕ Unit) :
    B.pentagonDegree i₁ i₂ j ∈ B.unfrozenBasis.positiveDegrees.monoid := by
  rcases j with i | ⟨⟩
  · exact B.unfrozenBasis_mem_positiveDegrees_monoid i
  · exact B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂

/-- The coefficients of the walls of the pentagon diagram at the unfrozen indices `i₁, i₂`,
for input coefficients `a`: `aᵢ` for the input wall at `i`, and `a_{i₁} a_{i₂}` for the outgoing
wall. -/
def pentagonCoefficient [Mul R] (a : B.unfrozenIndex → R) (i₁ i₂ : B.unfrozenIndex) :
    B.unfrozenIndex ⊕ Unit → R :=
  Sum.elim a fun _ => a i₁ * a i₂

/-- The coefficient of the input wall at `i` is `aᵢ`. -/
@[simp]
theorem pentagonCoefficient_inl [Mul R] (a : B.unfrozenIndex → R) (i₁ i₂ i : B.unfrozenIndex) :
    B.pentagonCoefficient a i₁ i₂ (.inl i) = a i := (rfl)

/-- The coefficient of the outgoing wall is `a_{i₁} a_{i₂}`. -/
@[simp]
theorem pentagonCoefficient_inr [Mul R] (a : B.unfrozenIndex → R) (i₁ i₂ : B.unfrozenIndex)
    (u : Unit) : B.pentagonCoefficient a i₁ i₂ (.inr u) = a i₁ * a i₂ := (rfl)

/-- The coefficient of each wall is the monomial weight of its degree. -/
theorem monomialWeight_pentagonDegree [CommMonoid R] (a : B.unfrozenIndex → R)
    (i₁ i₂ : B.unfrozenIndex) (j : B.unfrozenIndex ⊕ Unit) :
    B.unfrozenBasis.monomialWeight a (B.pentagonDegree i₁ i₂ j) =
      B.pentagonCoefficient a i₁ i₂ j := by
  rcases j with i | u
  · rw [pentagonDegree_inl, pentagonCoefficient_inl, Module.Basis.monomialWeight_self]
  · rw [pentagonDegree_inr, pentagonCoefficient_inr, Module.Basis.monomialWeight_add _ _
      (B.unfrozenBasis_mem_positiveDegrees_monoid i₁)
      (B.unfrozenBasis_mem_positiveDegrees_monoid i₂), Module.Basis.monomialWeight_self,
      Module.Basis.monomialWeight_self]

/-- The principal exponents `r(n)` of the wall degrees are principal positive degrees. -/
theorem principalEmbedding_pentagonDegree_mem (i₁ i₂ : B.unfrozenIndex)
    (j : B.unfrozenIndex ⊕ Unit) :
    D.principalEmbedding (B.pentagonDegree i₁ i₂ j) ∈
      (D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid := by
  rw [principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
  exact ⟨B.pentagonDegree_mem_positiveDegrees_monoid i₁ i₂ j, by simp⟩

/-- The principal exponent `r(n)` of the degree `n` of the wall indexed by `j`, as an element of
a coefficient monoid containing the principal positive degrees. -/
def pentagonExponent (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
    [Fact ((D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)]
    (i₁ i₂ : B.unfrozenIndex) (j : B.unfrozenIndex ⊕ Unit) : Q :=
  ⟨D.principalEmbedding (B.pentagonDegree i₁ i₂ j),
    (Fact.out : (D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)
      (B.principalEmbedding_pentagonDegree_mem i₁ i₂ j)⟩

/-- The principal exponent of the wall indexed by `j` is `r(n)`. -/
@[simp]
theorem coe_pentagonExponent (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
    [Fact ((D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)]
    (i₁ i₂ : B.unfrozenIndex) (j : B.unfrozenIndex ⊕ Unit) :
    (B.pentagonExponent Q i₁ i₂ j : Module.Dual ℤ D.sublattice × D.unfrozen) =
      D.principalEmbedding (B.pentagonDegree i₁ i₂ j) := (rfl)

/-- The indices of the walls of the pentagon diagram at the unfrozen indices `i₁, i₂` that are
not input walls at other unfrozen indices: the input walls at `i₁, i₂` and the outgoing wall. -/
def pentagonIndices (i₁ i₂ : B.unfrozenIndex) : Set (B.unfrozenIndex ⊕ Unit) :=
  {.inl i₁, .inl i₂, .inr ()}

/-- The indices in `pentagonIndices i₁ i₂` are `inl i₁`, `inl i₂` and `inr ()`. -/
theorem mem_pentagonIndices {i₁ i₂ : B.unfrozenIndex} {j : B.unfrozenIndex ⊕ Unit} :
    j ∈ B.pentagonIndices i₁ i₂ ↔ j = .inl i₁ ∨ j = .inl i₂ ∨ j = .inr () := by
  rw [pentagonIndices, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- An index outside `pentagonIndices i₁ i₂` is the input wall at an unfrozen index other than
`i₁, i₂`. -/
theorem exists_eq_inl_of_notMem_pentagonIndices {i₁ i₂ : B.unfrozenIndex}
    {j : B.unfrozenIndex ⊕ Unit} (hj : j ∉ B.pentagonIndices i₁ i₂) :
    ∃ i, i ≠ i₁ ∧ i ≠ i₂ ∧ j = .inl i := by
  rw [mem_pentagonIndices] at hj
  rcases j with i | ⟨⟩
  · exact ⟨i, fun h => hj (Or.inl (congrArg _ h)), fun h => hj (Or.inr (Or.inl (congrArg _ h))),
      rfl⟩
  · exact absurd (Or.inr (Or.inr rfl)) hj

/-- An adapted basis is *of type `A₂` with isolated indices* at the unfrozen indices `i₁, i₂`
when `{e_{i₁}, e_{i₂}} = 1`, every unfrozen multiplier is one, and every other unfrozen index is
isolated: its basis vector pairs to zero with every unfrozen basis vector. Frozen indices are
allowed, with arbitrary pairings. If `i₁, i₂` are the only unfrozen indices, the form on `N_uf` is
of type `A₂`; otherwise it is degenerate, and the isolated basis vectors lie in its radical. -/
structure IsTypeA₂WithIsolated (i₁ i₂ : B.unfrozenIndex) : Prop where
  /-- The skew pairing of the basis vectors at `i₁` and `i₂` is one. -/
  form_eq_one : D.form (B.basis i₁) (B.basis i₂) = 1
  /-- Every unfrozen multiplier is one. -/
  multiplier_eq_one (i : B.unfrozenIndex) : B.multiplier i = 1
  /-- Every unfrozen index other than `i₁, i₂` is isolated. -/
  form_eq_zero (i : B.unfrozenIndex) (hi₁ : i ≠ i₁) (hi₂ : i ≠ i₂) (j : B.unfrozenIndex) :
    D.form (B.basis i) (B.basis j) = 0

namespace IsTypeA₂WithIsolated

variable {B} {i₁ i₂ : B.unfrozenIndex} (hA : B.IsTypeA₂WithIsolated i₁ i₂)
include hA

/-- The multiplier at `i₁` is one. -/
theorem multiplier_fst : B.multiplier i₁ = 1 :=
  hA.multiplier_eq_one i₁

/-- The multiplier at `i₂` is one. -/
theorem multiplier_snd : B.multiplier i₂ = 1 :=
  hA.multiplier_eq_one i₂

/-- The basis vector at an isolated index pairs to zero with the degree of every wall of the
pentagon diagram. -/
theorem form_pentagonDegree_eq_zero {i : B.unfrozenIndex} (hi₁ : i ≠ i₁) (hi₂ : i ≠ i₂)
    (j : B.unfrozenIndex ⊕ Unit) : D.form (B.basis i) (B.pentagonDegree i₁ i₂ j : N) = 0 := by
  rcases j with j | ⟨⟩
  · rw [pentagonDegree_inl, coe_unfrozenBasis, hA.form_eq_zero i hi₁ hi₂ j]
  · rw [pentagonDegree_inr, Submodule.coe_add, coe_unfrozenBasis, coe_unfrozenBasis, map_add,
      hA.form_eq_zero i hi₁ hi₂, hA.form_eq_zero i hi₁ hi₂, add_zero]

/-- The two unfrozen indices are distinct. -/
theorem ne : i₁ ≠ i₂ := by
  rintro rfl
  simpa [D.form_self] using hA.form_eq_one

/-- The first unfrozen basis vector lies in `N°`. -/
theorem basis_fst_mem_sublattice : B.basis i₁ ∈ D.sublattice := by
  simpa [hA.multiplier_fst] using B.nsmul_basis_mem_sublattice i₁

/-- The second unfrozen basis vector lies in `N°`. -/
theorem basis_snd_mem_sublattice : B.basis i₂ ∈ D.sublattice := by
  simpa [hA.multiplier_snd] using B.nsmul_basis_mem_sublattice i₂

/-- The vector `e_{i₁} + e_{i₂}` is nonzero. -/
theorem add_ne_zero : B.unfrozenBasis i₁ + B.unfrozenBasis i₂ ≠ 0 := by
  intro h0
  have h := congrArg (B.unfrozenBasis.coord i₁) h0
  have hne : i₂ ≠ i₁ := hA.ne.symm
  simp [hne] at h

/-- The supported ray of the primitive allowed degree `e_{i₁} + e_{i₂}`. -/
def addRay : SupportedRay B.unfrozenBasis.positiveDegrees where
  generator := B.unfrozenBasis i₁ + B.unfrozenBasis i₂
  isPrimitive := TauCeti.isPrimitive_def.mpr ⟨B.unfrozenBasis.coord i₁, by
    have hne : i₂ ≠ i₁ := hA.ne.symm
    simp [hne]⟩
  supported := ⟨1, one_pos, by
    simpa using B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂⟩

/-- The generator of the supported ray is `e_{i₁} + e_{i₂}`. -/
@[simp]
theorem addRay_generator : hA.addRay.generator = B.unfrozenBasis i₁ + B.unfrozenBasis i₂ :=
  (rfl)

variable [Module.Free ℤ N]

/-- The normalized vector `κ(e_{i₁}) e_{i₁}` is `e_{i₁}`. -/
theorem coe_rayVector_fst :
    (D.sublattice.toAddSubgroup.rayVector (B.basis i₁) : N) = B.basis i₁ := by
  simp [hA.multiplier_fst]

/-- The normalized vector `κ(e_{i₂}) e_{i₂}` is `e_{i₂}`. -/
theorem coe_rayVector_snd :
    (D.sublattice.toAddSubgroup.rayVector (B.basis i₂) : N) = B.basis i₂ := by
  simp [hA.multiplier_snd]

/-- The sublattice coordinates dual to `e_{i₁}` and `e_{i₂}` evaluate on the normalized vectors
`κ(e_{i₁}) e_{i₁} = e_{i₁}` and `κ(e_{i₂}) e_{i₂} = e_{i₂}` as the identity matrix. -/
theorem coord_rayVector :
    B.sublatticeBasis.coord i₁ (D.sublattice.toAddSubgroup.rayVector (B.basis i₁)) = 1 ∧
      B.sublatticeBasis.coord i₁ (D.sublattice.toAddSubgroup.rayVector (B.basis i₂)) = 0 ∧
      B.sublatticeBasis.coord i₂ (D.sublattice.toAddSubgroup.rayVector (B.basis i₁)) = 0 ∧
      B.sublatticeBasis.coord i₂ (D.sublattice.toAddSubgroup.rayVector (B.basis i₂)) = 1 := by
  have hv : ∀ i : B.unfrozenIndex,
      D.sublattice.toAddSubgroup.rayVector (B.basis i) = B.sublatticeBasis i := fun i =>
    Subtype.ext (by rw [B.coe_rayVector_basis, coe_sublatticeBasis])
  have hne : (i₁ : ι) ≠ i₂ := fun he => hA.ne (Subtype.ext he)
  simp [hv, hne, hne.symm]

/-- The ray index of `e_{i₁} + e_{i₂}` is one, since this vector lies in `N°` and pairs to one
with `e_{i₁}`. -/
theorem rayIndex_add : D.sublattice.toAddSubgroup.rayIndex (B.basis i₁ + B.basis i₂) = 1 :=
  D.rayIndex_eq_one_of_form_eq_one (a := B.basis i₁)
    (add_mem (B.basis_mem_unfrozen i₁) (B.basis_mem_unfrozen i₂))
    (add_mem hA.basis_fst_mem_sublattice hA.basis_snd_mem_sublattice)
    (by simp [D.form_self, hA.form_eq_one])

/-- The normalized vector of `e_{i₁} + e_{i₂}` is the sum of those of `e_{i₁}` and `e_{i₂}`. -/
theorem rayVector_add :
    D.sublattice.toAddSubgroup.rayVector (B.basis i₁ + B.basis i₂) =
      D.sublattice.toAddSubgroup.rayVector (B.basis i₁) +
        D.sublattice.toAddSubgroup.rayVector (B.basis i₂) := by
  apply Subtype.ext
  have h := D.sublattice.toAddSubgroup.den_rayIndex_zsmul_rayVector (B.basis i₁ + B.basis i₂)
  rw [hA.rayIndex_add] at h
  simp only [Rat.den_one, Nat.cast_one, one_smul, Rat.num_one] at h
  rw [AddSubgroup.coe_add, h, hA.coe_rayVector_fst, hA.coe_rayVector_snd]

/-- The principal normal of `e_{i₁} + e_{i₂}` is the sum of those of `e_{i₁}` and `e_{i₂}`. -/
theorem principalNormal_add :
    D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂) =
      D.principalNormal (B.unfrozenBasis i₁) + D.principalNormal (B.unfrozenBasis i₂) := by
  apply LinearMap.ext
  intro x
  simp only [principalNormal_apply, Submodule.coe_add, coe_unfrozenBasis, hA.rayVector_add,
    map_add, LinearMap.add_apply]

/-- A character `χ` of `N°`, extended by zero on `N_uf`, on which the principal normal of
`e_{i₁} + e_{i₂}` vanishes and that of `e_{i₁}` is one. -/
theorem exists_principalNormal_add_eq_zero :
    ∃ χ : Module.Dual ℤ D.sublattice,
      D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂) (χ, 0) = 0 ∧
        D.principalNormal (B.unfrozenBasis i₁) (χ, 0) = 1 := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ := hA.coord_rayVector
  refine ⟨B.sublatticeBasis.coord i₁ - B.sublatticeBasis.coord i₂, ?_, ?_⟩
  · rw [hA.principalNormal_add]
    simp [h₁₁, h₁₂, h₂₁, h₂₂]
  · simp [h₁₁, h₂₁]

omit [Module.Free ℤ N] in
/-- The degrees of the walls are nonzero. -/
theorem pentagonDegree_ne_zero (j : B.unfrozenIndex ⊕ Unit) : B.pentagonDegree i₁ i₂ j ≠ 0 := by
  rcases j with i | ⟨⟩
  · exact B.unfrozenBasis.ne_zero i
  · exact hA.add_ne_zero

/-- The degrees of the walls have ray index one. -/
theorem rayIndex_pentagonDegree (j : B.unfrozenIndex ⊕ Unit) :
    D.sublattice.toAddSubgroup.rayIndex (B.pentagonDegree i₁ i₂ j : N) = 1 := by
  rcases j with i | ⟨⟩
  · simp [B.rayIndex_basis, hA.multiplier_eq_one i]
  · simpa using hA.rayIndex_add

/-- The principal normal of each wall degree takes the value one on some character `(χ, 0)`. -/
theorem exists_principalNormal_pentagonDegree_eq_one (j : B.unfrozenIndex ⊕ Unit) :
    ∃ χ : Module.Dual ℤ D.sublattice, D.principalNormal (B.pentagonDegree i₁ i₂ j) (χ, 0) = 1 := by
  obtain ⟨h₁₁, h₁₂, -, -⟩ := hA.coord_rayVector
  rcases j with i | ⟨⟩
  · exact B.exists_principalNormal_eq_one i
  · refine ⟨B.sublatticeBasis.coord i₁, ?_⟩
    rw [pentagonDegree_inr, hA.principalNormal_add]
    simp [h₁₁, h₁₂]

variable [CommRing R] [Algebra ℚ R]
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ D.sublattice × D.unfrozen) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) (a : B.unfrozenIndex → R)

local notation "𝒅" => B.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) 𝒅
local notation "e" => D.principalPositiveDegrees 𝒅
local notation "𝓗" => D.principalGraphWallSpaces (R := R) 𝒅

/-- The principal image of the ray label of `-Li₂(-a_{i₁} a_{i₂} T)` at `e_{i₁} + e_{i₂}`, as a
wall label on the principal graph ray through `r(e_{i₁} + e_{i₂})` with the principal normal of
`e_{i₁} + e_{i₂}`. For `a = 1` it is the dilogarithm element `Ψ[e_{i₁} + e_{i₂}]`. -/
def addLabel : (𝓗).wallGroup (hA.addRay.graph D.principalCharacter.toAddMonoidHom)
    (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom :=
  ⟨(𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
    (SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R)
      (B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂) hA.add_ne_zero
      (rescale (a i₁ * a i₂) (negDilogNeg R))), by
    rw [← D.map_principalGraphWallGroup, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact D.rayExp_mem_principalWallGroup (R := R) 𝒅
      ((SupportedRay.generator_mem_rayDegrees_iff _).mpr
        (B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂)) _⟩

/-- The outgoing label is the principal image of the ray label of `-Li₂(-a_{i₁} a_{i₂} T)` at
`e_{i₁} + e_{i₂}`. -/
@[simp]
theorem coe_addLabel : (hA.addLabel a).1 =
    (𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
      (SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R)
        (B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂) hA.add_ne_zero
        (rescale (a i₁ * a i₂) (negDilogNeg R))) :=
  (rfl)

/-- The outgoing wall of the pentagon diagram: the half-hyperplane of the principal normal `ν₁₂` of
`e_{i₁} + e_{i₂}` on which the principal normal `ν₁` of `e_{i₁}` is nonnegative, cooriented by
`ν₁₂`, on the principal ray through `r(e_{i₁} + e_{i₂})`, labelled by the principal image of the
ray label of `-Li₂(-a_{i₁} a_{i₂} T)` at `e_{i₁} + e_{i₂}`. -/
def outgoingWall : DirectedWall (V := V) (d := e) h 𝓗 :=
  (DirectedWall.ofAffineHyperplane h 𝓗
    (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom
    (fun hz => hA.add_ne_zero ((D.principalNormal_eq_zero_iff _).mp
      (LinearMap.toAddMonoidHom_injective hz))) 0
    (hA.addRay.graph D.principalCharacter.toAddMonoidHom)
    (by
      apply Int.cast_injective (α := ℚ)
      simp only [SupportedRay.graph_generator, addRay_generator, AddMonoidHom.id_apply,
        LinearMap.toAddMonoidHom_coe]
      rw [← D.principalEmbedding_apply, D.cast_principalNormal_principalEmbedding, D.form_self,
        mul_zero, Int.cast_zero])
    (hA.addLabel a)).cutHalfspace (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom 0 (by
      obtain ⟨χ, h₀, h₁⟩ := hA.exists_principalNormal_add_eq_zero
      exact ⟨latticeMap (χ, 0), by simp [h₀], by simp [h₁]⟩)

/-- The outgoing wall is cooriented by the principal normal of `e_{i₁} + e_{i₂}`. -/
@[simp]
theorem outgoingWall_normal : (hA.outgoingWall h a).normal =
    (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom := by
  simp [outgoingWall]

/-- The outgoing wall lies on the principal ray through `r(e_{i₁} + e_{i₂})`. -/
@[simp]
theorem outgoingWall_ray : (hA.outgoingWall h a).ray =
    hA.addRay.graph D.principalCharacter.toAddMonoidHom := by
  simp [outgoingWall]

/-- The support of the outgoing wall is the half-hyperplane `{ν₁₂ = 0, ν₁ ≥ 0}`. -/
@[simp]
theorem outgoingWall_support : (hA.outgoingWall h a).support =
    {x | h.realCharacter
        (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom x = 0} ∩
      {x | 0 ≤ h.realCharacter (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom x} := by
  simp [outgoingWall]

/-- The label of the outgoing wall is the principal image of the ray label of
`-Li₂(-a_{i₁} a_{i₂} T)` at `e_{i₁} + e_{i₂}`. -/
@[simp]
theorem outgoingWall_label : (hA.outgoingWall h a).label =
    (𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
      (SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R)
        (B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂) hA.add_ne_zero
        (rescale (a i₁ * a i₂) (negDilogNeg R))) := by
  rw [outgoingWall, DirectedWall.cutHalfspace_label, DirectedWall.ofAffineHyperplane_label,
    coe_addLabel]

/-- The outgoing wall is outgoing: the degree direction `r(e_{i₁} + e_{i₂})` pairs to
`{e_{i₁} + e_{i₂}, e_{i₁}} = -1` with `ν₁`, so it leaves the half-hyperplane. -/
theorem outgoingWall_outgoing : (hA.outgoingWall h a).Outgoing := by
  refine (DirectedWall.outgoing_iff _).mpr fun hrec => ?_
  have hinc := (DirectedWall.incoming_iff _).mpr (Set.mem_recessionCone.mp hrec)
  rw [outgoingWall, DirectedWall.incoming_cutHalfspace_iff _ _ _ _
    (DirectedWall.ofAffineHyperplane_incoming ..)] at hinc
  have hq : ((D.principalNormal (B.unfrozenBasis i₁) (D.principalEmbedding
      (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)) : ℤ) : ℚ) = -1 := by
    rw [D.cast_principalNormal_principalEmbedding]
    simp only [Submodule.coe_add, coe_unfrozenBasis, B.rayIndex_basis, hA.multiplier_fst,
      map_add, LinearMap.add_apply, D.form_self, D.form_swap (B.basis i₁), hA.form_eq_one]
    norm_num
  have hle' : 0 ≤ D.principalNormal (B.unfrozenBasis i₁) (D.principalEmbedding
      (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)) := by
    simpa [principalEmbedding_apply] using hinc
  have : (0 : ℚ) ≤ (D.principalNormal (B.unfrozenBasis i₁) (D.principalEmbedding
      (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)) : ℚ) := by exact_mod_cast hle'
  linarith

/-- The pentagon diagram with coefficients `a`: the walls of the adapted polynomial input with
`ℓ = 1` and coefficients `aᵢ`, of wall functions `1 + aᵢ q^{eᵢ}`, together with the outgoing
wall. -/
def pentagonDiagram : DirectedDiagram (V := V) (d := e) h 𝓗 (B.unfrozenIndex ⊕ Unit) :=
  DirectedDiagram.ofFinite (Sum.elim (B.adaptedPolynomialInput (V := V) (fun _ => 1)
    (fun i _ => a i) h).wall fun _ => hA.outgoingWall h a)

/-- The walls indexed by the unfrozen indices are those of the adapted polynomial input. -/
@[simp]
theorem pentagonDiagram_wall_inl (i : B.unfrozenIndex) :
    (hA.pentagonDiagram h a).wall (.inl i) =
      (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun i _ => a i) h).wall i := by
  simp [pentagonDiagram]

/-- The remaining wall is the outgoing wall. -/
@[simp]
theorem pentagonDiagram_wall_inr (u : Unit) :
    (hA.pentagonDiagram h a).wall (.inr u) = hA.outgoingWall h a := by
  simp [pentagonDiagram]

/-- The wall of the pentagon diagram indexed by `j` has the principal normal of
`pentagonDegree i₁ i₂ j`. -/
theorem pentagonDiagram_normal (j : B.unfrozenIndex ⊕ Unit) :
    ((hA.pentagonDiagram h a).wall j).normal =
      (D.principalNormal (B.pentagonDegree i₁ i₂ j)).toAddMonoidHom := by
  rcases j with i | ⟨⟩ <;> simp

/-- The label of the wall of the pentagon diagram indexed by `j` is the principal image of the ray
label of `-Li₂(-c T)` at `n`, for `n = pentagonDegree i₁ i₂ j` and
`c = pentagonCoefficient a i₁ i₂ j`. -/
theorem pentagonDiagram_label (j : B.unfrozenIndex ⊕ Unit) :
    ((hA.pentagonDiagram h a).wall j).label =
      (𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
        (SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R)
          (B.pentagonDegree_mem_positiveDegrees_monoid i₁ i₂ j) (hA.pentagonDegree_ne_zero j)
          (rescale (B.pentagonCoefficient a i₁ i₂ j) (negDilogNeg R))) := by
  rcases j with i | u
  · rw [pentagonDiagram_wall_inl, adaptedPolynomialInput_label,
      B.coe_polynomialWallLabel_of_multiplier_eq_one _ (hA.multiplier_eq_one i),
      pentagonCoefficient_inl]
    exact congrArg _ (SkewLieAlgebra.rayExp_congr_degree _ _
      (B.pentagonDegree_inl i₁ i₂ i).symm _ _ _ _ _)
  · rw [pentagonDiagram_wall_inr, outgoingWall_label, pentagonCoefficient_inr]
    exact congrArg _ (SkewLieAlgebra.rayExp_congr_degree _ _
      (B.pentagonDegree_inr i₁ i₂ u).symm _ _ _ _ _)

/-- The label of the input wall at an isolated index commutes with every label of the pentagon
diagram. -/
theorem commute_pentagonDiagram_label {i : B.unfrozenIndex} (hi₁ : i ≠ i₁) (hi₂ : i ≠ i₂)
    (j : B.unfrozenIndex ⊕ Unit) :
    Commute ((hA.pentagonDiagram h a).wall (.inl i)).label
      ((hA.pentagonDiagram h a).wall j).label := by
  rw [pentagonDiagram_label, pentagonDiagram_label]
  refine (SkewLieAlgebra.commute_rayExp_of_eq_zero _ _ _ _ _ _ ?_ _ _).map _
  rw [coefficientForm_apply, pentagonDegree_inl, coe_unfrozenBasis,
    hA.form_pentagonDegree_eq_zero hi₁ hi₂, map_zero]

/-- The walls of the pentagon diagram at `inl i₁`, `inl i₂` and `inr ()` are in pentagon
configuration: they are the hyperplanes of the principal normals `ν₁, ν₂` of `e_{i₁}, e_{i₂}`
and the half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}` cooriented by `ν₁ + ν₂`. -/
theorem isPentagonConfiguration :
    ((hA.pentagonDiagram h a).restrict (B.pentagonIndices i₁ i₂)).IsPentagonConfiguration
      ⟨.inl i₁, B.mem_pentagonIndices.mpr (Or.inl rfl)⟩
      ⟨.inl i₂, B.mem_pentagonIndices.mpr (Or.inr (Or.inl rfl))⟩
      ⟨.inr (), B.mem_pentagonIndices.mpr (Or.inr (Or.inr rfl))⟩
      (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom
      (D.principalNormal (B.unfrozenBasis i₂)).toAddMonoidHom := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ := hA.coord_rayVector
  have hadd : (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom =
      (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom +
        (D.principalNormal (B.unfrozenBasis i₂)).toAddMonoidHom := by
    ext x
    simp [hA.principalNormal_add]
  refine
    { eq_or_eq_or_eq := ?_
      normal_fst := by simp
      normal_snd := by simp
      normal_half := by simp [hadd]
      support_fst := by ext; simp
      support_snd := by ext; simp
      support_half := by ext; simp [hadd]
      exists_fst := ⟨latticeMap (B.sublatticeBasis.coord i₂, 0), by simp [h₂₁], by simp [h₂₂]⟩
      exists_snd := ⟨latticeMap (B.sublatticeBasis.coord i₁, 0), by simp [h₁₂], by simp [h₁₁]⟩ }
  rintro ⟨j, hj⟩
  rcases B.mem_pentagonIndices.mp hj with rfl | rfl | rfl
  exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]

/-- The labels of the pentagon diagram satisfy the pentagon relation with coefficients
`Ψ_{a_{i₂}}[e_{i₂}] Ψ_{a_{i₁}}[e_{i₁}] =
Ψ_{a_{i₁}}[e_{i₁}] Ψ_{a_{i₁} a_{i₂}}[e_{i₁} + e_{i₂}] Ψ_{a_{i₂}}[e_{i₂}]`, where `Ψ_c[n]` is the ray
label of `-Li₂(-c T)` at `n`. -/
theorem pentagonDiagram_label_pentagon :
    ((hA.pentagonDiagram h a).wall (.inl i₂)).label *
        ((hA.pentagonDiagram h a).wall (.inl i₁)).label =
      ((hA.pentagonDiagram h a).wall (.inl i₁)).label *
        ((hA.pentagonDiagram h a).wall (.inr ())).label *
        ((hA.pentagonDiagram h a).wall (.inl i₂)).label := by
  simp only [pentagonDiagram_wall_inl, pentagonDiagram_wall_inr, adaptedPolynomialInput_label,
    outgoingWall_label, B.coe_polynomialWallLabel_of_multiplier_eq_one _ hA.multiplier_fst,
    B.coe_polynomialWallLabel_of_multiplier_eq_one _ hA.multiplier_snd, ← map_mul]
  congr 1
  have hp := SkewLieAlgebra.rayExp_rescale_smul_negDilogNeg_pentagon (D.coefficientForm R)
    (D.isAlt_coefficientForm R) 𝒅 (fun _ hn _ hm => B.unfrozenBasis.monomialWeight_add a hn hm)
    (B.unfrozenBasis_mem_positiveDegrees_monoid i₁) (B.unfrozenBasis_mem_positiveDegrees_monoid i₂)
    (B.unfrozenBasis.ne_zero i₁) (B.unfrozenBasis.ne_zero i₂) (c := 1)
    (by rw [one_mul, coefficientForm_apply, coe_unfrozenBasis, coe_unfrozenBasis, hA.form_eq_one,
      map_one])
  simpa only [one_smul, Module.Basis.monomialWeight_self] using hp

/-- The input walls of the pentagon diagram at the isolated indices form a consistent diagram: they
are full hyperplanes with commuting labels. -/
theorem restrict_compl_pentagonIndices_consistent :
    ((hA.pentagonDiagram h a).restrict (B.pentagonIndices i₁ i₂)ᶜ).Consistent := by
  refine DirectedDiagram.consistent_of_commute_of_full _ (fun j => ?_) fun j j' => ?_
  · obtain ⟨i, -, -, hi⟩ := B.exists_eq_inl_of_notMem_pentagonIndices j.property
    rw [DirectedDiagram.restrict_wall, hi, pentagonDiagram_wall_inl]
    exact B.adaptedPolynomialInput_full _ _ h i
  · obtain ⟨i, hi₁, hi₂, hi⟩ := B.exists_eq_inl_of_notMem_pentagonIndices j.property
    rw [DirectedDiagram.restrict_wall, DirectedDiagram.restrict_wall, hi]
    exact hA.commute_pentagonDiagram_label h a hi₁ hi₂ _

/-- The pentagon diagram is consistent. -/
theorem pentagonDiagram_consistent : (hA.pentagonDiagram h a).Consistent := by
  refine DirectedDiagram.consistent_of_restrict_of_restrict_compl
    ((hA.isPentagonConfiguration h a).consistent ?_)
    (hA.restrict_compl_pentagonIndices_consistent h a) fun j _ j' hj' => ?_
  · simpa only [DirectedDiagram.restrict_wall] using hA.pentagonDiagram_label_pentagon h a
  · obtain ⟨i, hi₁, hi₂, rfl⟩ := B.exists_eq_inl_of_notMem_pentagonIndices hj'
    exact (hA.commute_pentagonDiagram_label h a hi₁ hi₂ j).symm

/-- The pentagon diagram is an outgoing completion of the adapted polynomial input with `ℓ = 1`
and coefficients `aᵢ`: its walls at the unfrozen indices are the input walls, its remaining wall
is outgoing, and it is consistent. -/
theorem isOutgoingCompletion_pentagonDiagram :
    DirectedDiagram.IsOutgoingCompletion
      (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun i _ => a i) h).wall
      (hA.pentagonDiagram h a) where
  wall_inl := hA.pentagonDiagram_wall_inl h a
  outgoing_inr _ := by
    rw [pentagonDiagram_wall_inr]
    exact hA.outgoingWall_outgoing h a
  consistent := hA.pentagonDiagram_consistent h a

/-- **The scattering diagram of type `A₂` with isolated indices and coefficients.** For an adapted
basis of type `A₂` with isolated indices and coefficients `aᵢ`, the outgoing scattering class of
the adapted polynomial input `(eᵢ⊥, 1 + aᵢ q^{eᵢ})` on the principal lattice, over all unfrozen
indices `i`, is the class of the pentagon diagram, with the one additional outgoing wall
`{ν₁ + ν₂ = 0, ν₁ ≥ 0}` labelled by the ray label of `-Li₂(-a_{i₁} a_{i₂} T)` at
`e_{i₁} + e_{i₂}`. For `a = 1` the input is the ordinary binomial input and the new label is
`Ψ[e_{i₁} + e_{i₂}]`. -/
theorem scat_eq_toClass_pentagonDiagram
    [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)] :
    (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun i _ => a i) h).Scat
        (B.adaptedPolynomialInput_full _ _ h) = (hA.pentagonDiagram h a).toClass :=
  DirectedDiagram.scat_eq_toClass _ _ (hA.isOutgoingCompletion_pentagonDiagram h a)

variable [AddCommGroup M] (π : Module.Dual ℤ D.sublattice × D.unfrozen →+ M)

/-- The coorientations of the walls of the pentagon diagram are primitive. -/
theorem isPrimitive_pentagonDiagram_normal (j : B.unfrozenIndex ⊕ Unit) :
    TauCeti.IsPrimitive ((hA.pentagonDiagram h a).wall j).normal := by
  have := Module.Free.of_basis B.sublatticeBasis
  have hp := ((addMonoidHomLequivInt (B := ℤ) ℤ).symm.isPrimitive_iff).mpr
    (D.isPrimitive_principalNormal (hA.pentagonDegree_ne_zero j))
  rwa [addMonoidHomLequivInt_symm_apply, ← hA.pentagonDiagram_normal h a j] at hp

variable (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q
local notation "σ" => MonoidHom.comp (AlgFiltration.completedBCHAction (F) e
  (tropicalVertexGrading (R := R) e (AddMonoidHom.id Lpr)))
  (GradedLieHom.completedMap (D.principalGraphGradedLieHom (R := R) 𝒅))

/-- The principal monomial `z^{r(n)}` of the degree `n` of the wall indexed by `j`, in the first
ideal of the completed coefficient algebra. -/
def pentagonMonomial (j : B.unfrozenIndex ⊕ Unit) : (F).completionIdeal 1 :=
  ⟨(F).toCompletion (single (B.pentagonExponent Q i₁ i₂ j) 1),
    D.toCompletion_single_principalEmbedding_mem_first 𝒅
      (B.pentagonDegree_mem_positiveDegrees_monoid i₁ i₂ j) (hA.pentagonDegree_ne_zero j) Q _
      (B.coe_pentagonExponent Q i₁ i₂ j)⟩

omit [Module.Free ℤ N] [Algebra ℚ R] [DecidableEq D.unfrozen]
  [DecidableEq (Module.Dual ℤ D.sublattice)] in
/-- The principal monomial of the wall indexed by `j` is the image of `z^{r(n)}`. -/
@[simp]
theorem coe_pentagonMonomial (j : B.unfrozenIndex ⊕ Unit) :
    (hA.pentagonMonomial (R := R) Q j).val =
      (F).toCompletion (single (B.pentagonExponent Q i₁ i₂ j) 1) := (rfl)

/-- The wall function `1 + c z^{r(n)}` of the wall indexed by `j`, for its degree `n` and its
coefficient `c` (`aᵢ` on the input wall at `i`, `a_{i₁} a_{i₂}` on the outgoing wall), as a unit
of the completed coefficient algebra. -/
def pentagonWallFunction (j : B.unfrozenIndex ⊕ Unit) : (F).completionˣ :=
  ((F).isUnit_of_sub_one_mem ((F).completedAeval_sub_one_mem_first (hA.pentagonMonomial Q j)
    (1 + C (B.pentagonCoefficient a i₁ i₂ j) * X) (by simp))).unit

omit [Module.Free ℤ N] [Algebra ℚ R] [DecidableEq D.unfrozen]
  [DecidableEq (Module.Dual ℤ D.sublattice)] in
/-- The wall function of the wall indexed by `j` is `1 + c z^{r(n)}`. -/
theorem coe_pentagonWallFunction (j : B.unfrozenIndex ⊕ Unit) :
    (hA.pentagonWallFunction a Q j : (F).completion) =
      1 + (F).toCompletion
        (single (B.pentagonExponent Q i₁ i₂ j) (B.pentagonCoefficient a i₁ i₂ j)) :=
  (IsUnit.unit_spec _).trans
    (AlgFiltration.completedAeval_one_add_C_mul_X_of_val_eq_toCompletion_single
      (hA.coe_pentagonMonomial Q j) _)

omit [Module.Free ℤ N] [Algebra ℚ R] [DecidableEq D.unfrozen]
  [DecidableEq (Module.Dual ℤ D.sublattice)] in
/-- The wall function of the input wall at the unfrozen index `i` is `1 + aᵢ z^{r(eᵢ)}`. -/
theorem coe_pentagonWallFunction_inl (i : B.unfrozenIndex) :
    (hA.pentagonWallFunction a Q (.inl i) : (F).completion) =
      1 + (F).toCompletion (single (B.pentagonExponent Q i₁ i₂ (.inl i)) (a i)) := by
  rw [coe_pentagonWallFunction, pentagonCoefficient_inl]

omit [Module.Free ℤ N] [Algebra ℚ R] [DecidableEq D.unfrozen]
  [DecidableEq (Module.Dual ℤ D.sublattice)] in
/-- The wall function of the outgoing wall is `1 + a_{i₁} a_{i₂} z^{r(e_{i₁} + e_{i₂})}`. -/
theorem coe_pentagonWallFunction_inr (u : Unit) :
    (hA.pentagonWallFunction a Q (.inr u) : (F).completion) =
      1 + (F).toCompletion (single (B.pentagonExponent Q i₁ i₂ (.inr u)) (a i₁ * a i₂)) := by
  rw [coe_pentagonWallFunction, pentagonCoefficient_inr]

/-- If the coefficient monoid `Q` contains every character `(χ, 0)`, then in the discrete grouping
of the pentagon diagram, in which every wall is its own function wall, the wall indexed by `j`
has the wall function `1 + c z^{r(n)}` (`pentagonWallFunction`): `1 + aᵢ q^{eᵢ}` on the input wall
at `i` and `1 + a_{i₁} a_{i₂} q^{e_{i₁} + e_{i₂}}` on the outgoing wall. -/
theorem isWallFunction_discrete_pentagonDiagram
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) (j : B.unfrozenIndex ⊕ Unit) :
    (DirectedDiagram.FunctionWallGrouping.discrete (hA.pentagonDiagram h a)
      (hA.isPrimitive_pentagonDiagram_normal h a) π).IsWallFunction σ j
      (hA.pentagonWallFunction a Q j) := by
  -- Destructuring with `obtain` re-elaborates the goal and times out.
  let χ := (hA.exists_principalNormal_pentagonDegree_eq_one j).choose
  have hχ := (hA.exists_principalNormal_pentagonDegree_eq_one j).choose_spec
  have hν := hA.pentagonDiagram_normal h a j
  refine DirectedDiagram.FunctionWallGrouping.isWallFunction_discrete σ _
    (p := ⟨(χ, 0), hQ χ⟩) (by rw [hν]; exact hχ)
    (TropicalVertexCoefficientAction.isUnit_toCompletion_single (hQ χ) (by simpa using hQ (-χ)))
    fun p c => ?_
  -- The label and the normal are transported by `congrArg`: rewriting them with `rw` in
  -- goals containing the completed coefficient algebra times out.
  refine (congrArg (fun g => (σ) g ((F).toCompletion (single p c)))
      (hA.pentagonDiagram_label h a j)).trans
    ((B.completedBCHAction_graphBCHGroupEquiv_rayExp_rescale_negDilogNeg Q
      (B.pentagonDegree_mem_positiveDegrees_monoid i₁ i₂ j) (hA.pentagonDegree_ne_zero j)
      (hA.rayIndex_pentagonDegree j) _ _ (B.coe_pentagonExponent Q i₁ i₂ j) _
      (hA.coe_pentagonWallFunction a Q j) p c).trans ?_)
  exact congrArg (fun k : ℤ => ((hA.pentagonWallFunction a Q j ^ k : (F).completionˣ) :
    (F).completion) * (F).toCompletion (single p c))
    (congrArg (fun ν : Lpr →+ ℤ => ν p.val) hν).symm

/-- If the coefficient monoid `Q` contains every character `(χ, 0)` and the coefficients `aᵢ`
are images of elements of `S` under a semiring map `φ : S →+* R`, the discrete
grouping of the pentagon diagram is positive for the image of `S[Q]`. -/
theorem isPositive_discrete_pentagonDiagram
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) {S : Type*} [Semiring S]
    (φ : S →+* R) (ha : ∀ i, a i ∈ φ.rangeS) :
    (DirectedDiagram.FunctionWallGrouping.discrete (hA.pentagonDiagram h a)
      (hA.isPrimitive_pentagonDiagram_normal h a) π).IsPositive σ (mapRingHom Q φ).rangeS := by
  refine (DirectedDiagram.FunctionWallGrouping.isPositive_iff _ _ _).mpr fun j =>
    ⟨_, hA.isWallFunction_discrete_pentagonDiagram h a π Q hQ j, ?_⟩
  obtain ⟨b, hb⟩ := B.monomialWeight_pentagonDegree a i₁ i₂ j ▸
    B.unfrozenBasis.monomialWeight_mem a ha (B.pentagonDegree i₁ i₂ j)
  rw [coe_pentagonWallFunction, ← map_one (F).toCompletion, ← map_add]
  exact AlgFiltration.isPositive_toCompletion
    (add_mem (one_mem _) ⟨single _ b, by rw [mapRingHom_single, hb]⟩)

/-- Under the hypotheses of `isPositive_discrete_pentagonDiagram`, the pentagon diagram is a
positive wall representative for the image of `S[Q]`. -/
theorem isPositiveWallRepresentative_pentagonDiagram
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) {S : Type*} [Semiring S]
    (φ : S →+* R) (ha : ∀ i, a i ∈ φ.rangeS) :
    (hA.pentagonDiagram h a).IsPositiveWallRepresentative σ (mapRingHom Q φ).rangeS π :=
  (hA.isPositive_discrete_pentagonDiagram h a π Q hQ φ ha).isPositiveWallRepresentative

/-- **Positivity of adapted polynomial walls of type `A₂` with isolated indices.** For an adapted
basis of type `A₂` with isolated indices, coefficients `aᵢ` that are images under a semiring map
`φ : S →+* R`, and a coefficient monoid `Q` containing every character `(χ, 0)`, the outgoing
scattering class of the adapted polynomial input `(eᵢ⊥, 1 + aᵢ q^{eᵢ})` on the principal lattice,
over all unfrozen indices `i`, has a consistent outgoing representative, the pentagon diagram,
whose grouped wall functions `1 + aᵢ q^{eᵢ}` and `1 + a_{i₁} a_{i₂} q^{e_{i₁} + e_{i₂}}` are
positive for the image of `S[Q]`. For `a = 1` and `φ = Nat.castRingHom R` this is the ordinary
binomial input with natural-number coefficients. -/
theorem exists_isPositiveWallRepresentative_scat
    [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)]
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) {S : Type*} [Semiring S]
    (φ : S →+* R) (ha : ∀ i, a i ∈ φ.rangeS) :
    ∃ (κ : Type) (E : DirectedDiagram (V := V) (d := e) h 𝓗 (B.unfrozenIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion
        (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun i _ => a i) h).wall E ∧
      E.toClass = (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun i _ => a i) h).Scat
        (B.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative σ (mapRingHom Q φ).rangeS π :=
  ⟨Unit, hA.pentagonDiagram h a, hA.isOutgoingCompletion_pentagonDiagram h a,
    (hA.scat_eq_toClass_pentagonDiagram h a).symm,
    hA.isPositiveWallRepresentative_pentagonDiagram h a π Q hQ φ ha⟩

end IsTypeA₂WithIsolated

end Mei.SkewLatticeDatum.AdaptedBasis
