/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Principal
public import Mei.Algebra.Lie.Logarithmic.Grading

/-!
# Principal logarithmic realization of a skew lattice datum

The principal field associated to an unfrozen degree `n` is `z^(p₁*(n),n) ∂_νₙ`,
where `νₙ(m,a) = ⟨n,m⟩` uses the rational extension of the integral character `m`
from the finite-index sublattice. These fields satisfy the skew Lie bracket
`[Xₙ,Xₙ'] = {n',n} Xₙ₊ₙ'`. Assuming `Module.Free ℤ N`, their nonzero-degree generators
are linearly independent, even for a degenerate or zero skew form. Under this assumption,
linear combinations give a faithful formal principal realization away from degree zero
without imposing nondegeneracy on the skew form. Casting the integral principal normal
to coefficients gives the ray index times this rational evaluation character.

We use `LogarithmicVectorField.single_bracket_single`, its coefficient equivalence,
and Mathlib's `Finsupp.linearCombination`. The principal realization follows
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open LogarithmicVectorField

variable {N R : Type*} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  (D : SkewLatticeDatum N)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen

/-- The rational principal normal, with values in the coefficient algebra.
It evaluates the character coordinate on `n`, extending from `N°` by division
by its finite index. The unfrozen coordinate does not enter the evaluation. -/
def principalEvaluation : D.unfrozen →ₗ[ℤ] (Lpr →+ R) :=
  ({
    toFun n :=
      { toFun := fun x => algebraMap ℚ R
          ((D.sublattice.toAddSubgroup.index : ℚ)⁻¹ *
            x.1 ⟨D.sublattice.toAddSubgroup.index • (n : N),
              D.sublattice.toAddSubgroup.nsmul_index_mem n⟩)
        map_zero' := by simp
        map_add' := by intros; simp [mul_add] }
    map_zero' := by
      ext x
      have hz : (⟨D.sublattice.toAddSubgroup.index • (0 : N),
          D.sublattice.toAddSubgroup.nsmul_index_mem 0⟩ : D.sublattice) = 0 := by
        ext; simp
      -- Expose the bundled evaluation to rewrite its zero sublattice argument.
      change algebraMap ℚ R ((D.sublattice.toAddSubgroup.index : ℚ)⁻¹ *
        x.1 ⟨D.sublattice.toAddSubgroup.index • (0 : N), _⟩) = 0
      rw [hz]
      simp
    map_add' n n' := by
      ext x
      have he : (⟨D.sublattice.toAddSubgroup.index • ((n : N) + n'),
          D.sublattice.toAddSubgroup.nsmul_index_mem ((n : N) + n')⟩ : D.sublattice) =
        ⟨D.sublattice.toAddSubgroup.index • (n : N),
          D.sublattice.toAddSubgroup.nsmul_index_mem n⟩ +
        ⟨D.sublattice.toAddSubgroup.index • (n' : N),
          D.sublattice.toAddSubgroup.nsmul_index_mem n'⟩ := by
        ext; exact nsmul_add _ _ _
      -- These are the linearity laws of the bundled normal; expose both evaluations.
      change algebraMap ℚ R ((D.sublattice.toAddSubgroup.index : ℚ)⁻¹ *
        x.1 ⟨D.sublattice.toAddSubgroup.index • ((n : N) + n'), _⟩) =
        algebraMap ℚ R ((D.sublattice.toAddSubgroup.index : ℚ)⁻¹ *
          x.1 ⟨D.sublattice.toAddSubgroup.index • (n : N), _⟩) +
        algebraMap ℚ R ((D.sublattice.toAddSubgroup.index : ℚ)⁻¹ *
          x.1 ⟨D.sublattice.toAddSubgroup.index • (n' : N), _⟩)
      simpa only [map_add, Int.cast_add, mul_add] using
        congrArg (fun v : D.sublattice => algebraMap ℚ R
          ((D.sublattice.toAddSubgroup.index : ℚ)⁻¹ * (x.1 v : ℚ))) he
  } : D.unfrozen →+ (Lpr →+ R)).toIntLinearMap

/-- The principal normal evaluates by dividing the integral character value
on the index multiple of `n` by that index. -/
theorem principalEvaluation_apply (n : D.unfrozen) (x : Lpr) :
    D.principalEvaluation (R := R) n x = algebraMap ℚ R
      ((D.sublattice.toAddSubgroup.index : ℚ)⁻¹ *
        x.1 ⟨D.sublattice.toAddSubgroup.index • (n : N),
          D.sublattice.toAddSubgroup.nsmul_index_mem n⟩) := (rfl)

/-- Normal evaluation at a principal exponent recovers the skew pairing, with
order reversed relative to the field indices. -/
@[simp]
theorem principalEvaluation_principalEmbedding (n n' : D.unfrozen) :
    D.principalEvaluation (R := R) n (D.principalCharacter n', n') =
      algebraMap ℚ R (D.form n' n) := by
  have hi : (D.sublattice.toAddSubgroup.index : ℚ) ≠ 0 := by
    exact_mod_cast (AddSubgroup.index_ne_zero (H := D.sublattice.toAddSubgroup))
  rw [principalEvaluation_apply, D.cast_principalCharacter_apply]
  simp only [map_nsmul, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hi, one_mul]

/-- On a character restricted from the ambient lattice, rational extension
recovers its original integral evaluation. -/
@[simp]
theorem principalEvaluation_restrict (n : D.unfrozen) (φ : Module.Dual ℤ N)
    (a : D.unfrozen) :
    D.principalEvaluation (R := R) n (φ.comp D.sublattice.subtype, a) =
      algebraMap ℚ R (φ n : ℚ) := by
  have hi : (D.sublattice.toAddSubgroup.index : ℚ) ≠ 0 := by
    exact_mod_cast (AddSubgroup.index_ne_zero (H := D.sublattice.toAddSubgroup))
  rw [principalEvaluation_apply]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_nsmul,
    nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ hi, one_mul]

section Free

variable [Module.Free ℤ N]

/-- Casting the normalized integral normal to coefficients multiplies the rational
principal evaluation character by the ray index `κ(n)`. -/
theorem intCast_principalNormal_apply
    (n : D.unfrozen) (x : Module.Dual ℤ D.sublattice × D.unfrozen) :
    (D.principalNormal n x : R) =
      algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex n) *
        D.principalEvaluation (R := R) n x := by
  have heval : (D.principalNormal n x : ℚ) =
      D.sublattice.toAddSubgroup.rayIndex n * D.principalEvaluation (R := ℚ) n x := by
    let I := D.sublattice.toAddSubgroup.index
    let κ := D.sublattice.toAddSubgroup.rayIndex n
    have hi : (I : ℚ) ≠ 0 := by
      exact_mod_cast (AddSubgroup.index_ne_zero (H := D.sublattice.toAddSubgroup))
    have hd : (κ.den : ℚ) ≠ 0 := by positivity
    have he : (κ.den : ℤ) • (I • D.sublattice.toAddSubgroup.rayVector n) =
        κ.num • (⟨I • (n : N), D.sublattice.toAddSubgroup.nsmul_index_mem n⟩ :
          D.sublattice) := by
      apply Subtype.ext
      simp only [AddSubgroup.coe_zsmul, AddSubgroup.coe_nsmul, Submodule.coe_smul_of_tower]
      rw [smul_comm, D.sublattice.toAddSubgroup.den_rayIndex_zsmul_rayVector,
        smul_comm]
    have hφ := congrArg x.1 he
    simp only [map_zsmul, map_nsmul, zsmul_eq_mul, nsmul_eq_mul] at hφ
    have hφQ : (κ.den : ℚ) * (I * (x.1 (D.sublattice.toAddSubgroup.rayVector n) : ℚ)) =
        κ.num * (x.1 ⟨I • (n : N), D.sublattice.toAddSubgroup.nsmul_index_mem n⟩ : ℚ) := by
      exact_mod_cast hφ
    dsimp only [κ, I] at hφQ
    rw [principalNormal_apply, principalEvaluation_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Rat.num_div_den (D.sublattice.toAddSubgroup.rayIndex n)]
    dsimp only [κ, I] at hi hd ⊢
    field_simp
    nlinarith [hφQ]
  have h := congrArg (algebraMap ℚ R) heval
  simpa only [map_intCast, map_mul, principalEvaluation_apply, Algebra.algebraMap_self,
    RingHom.id_apply] using h

/-- A nonzero principal normal has no scalar torsion over any rational
coefficient algebra, including coefficient algebras with zero divisors. -/
@[simp]
theorem smul_principalEvaluation_eq_zero_iff {n : D.unfrozen} (hn : n ≠ 0) (c : R) :
    c • D.principalEvaluation (R := R) n = 0 ↔ c = 0 := by
  constructor
  · intro he
    have hnN : (n : N) ≠ 0 := fun h => hn (Subtype.ext h)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℤ N, φ n ≠ 0 := by
      simpa only [not_forall] using
        mt (Module.forall_dual_apply_eq_zero_iff ℤ (n : N)).mp hnN
    have hc := DFunLike.congr_fun he (φ.comp D.sublattice.subtype, 0)
    simp only [AddMonoidHom.smul_apply, principalEvaluation_restrict,
      AddMonoidHom.zero_apply, smul_eq_mul] at hc
    have hu : IsUnit (algebraMap ℚ R (φ n : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hφ)).map (algebraMap ℚ R)
    exact hu.mul_left_eq_zero.mp hc
  · rintro rfl
    exact zero_smul _ _

end Free

/-- The principal field `Xₙ = z^(r(n)) ∂_νₙ`. The zero degree gives the zero field. -/
def principalField (n : D.unfrozen) : LogarithmicVectorField R Lpr Lpr (AddMonoidHom.id Lpr) :=
  single (AddMonoidHom.id Lpr) (D.principalEmbedding n) (D.principalEvaluation n)

/-- The principal field has the prescribed exponent and character. -/
@[simp]
theorem toFinsupp_principalField (n : D.unfrozen) :
    toFinsupp (AddMonoidHom.id Lpr) (D.principalField (R := R) n) =
      Finsupp.single (D.principalEmbedding n) (D.principalEvaluation n) := by
  simp [principalField]

@[simp]
theorem principalField_zero : D.principalField (R := R) 0 = 0 := by
  simp [principalField]

/-- Principal fields are tangent to their own exponents. -/
theorem principalField_mem_tangentGrade (n : D.unfrozen) :
    D.principalField (R := R) n ∈ tangentGrade (AddMonoidHom.id Lpr)
      (D.principalEmbedding n) := by
  rw [principalField, single_mem_tangentGrade_iff]
  simpa only [principalEmbedding_apply, AddMonoidHom.id_apply, form_self, map_zero] using
    D.principalEvaluation_principalEmbedding (R := R) n n

/-- The principal logarithmic realization has the skew Lie bracket, including
when either exponent or their sum is in the radical of the form. -/
@[simp]
theorem lie_principalField (n n' : D.unfrozen) :
    ⁅D.principalField (R := R) n, D.principalField (R := R) n'⁆ =
      algebraMap ℚ R (D.form n' n) • D.principalField (R := R) (n + n') := by
  simp only [principalField, single_bracket_single, AddMonoidHom.id_apply,
    principalEmbedding_apply, principalEvaluation_principalEmbedding]
  rw [D.principalCharacter.map_add,
    ← (single (R := R) (AddMonoidHom.id Lpr) _).map_smul]
  congr 1
  ext x
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, smul_eq_mul,
    map_add, AddMonoidHom.add_apply]
  rw [D.form_swap n' n, map_neg]
  ring

/-- Extend the principal generators linearly to arbitrary finite coefficient families.
The coefficient at degree zero is killed; assuming `Module.Free ℤ N`, all other
coefficients are retained. -/
def principalRealization : (D.unfrozen →₀ R) →ₗ[R]
    LogarithmicVectorField R Lpr Lpr (AddMonoidHom.id Lpr) :=
  Finsupp.linearCombination R D.principalField

/-- A singleton coefficient gives the corresponding scalar multiple of the field. -/
@[simp]
theorem principalRealization_single (n : D.unfrozen) (c : R) :
    D.principalRealization (Finsupp.single n c) = c • D.principalField n := by
  simp [principalRealization]

/-- The formal coefficient at `r(n)` is the input coefficient times `νₙ`.
Injectivity of the principal exponent map prevents any other degree contributing. -/
@[simp]
theorem principalRealization_coeff (f : D.unfrozen →₀ R) (n : D.unfrozen) :
    toFinsupp (AddMonoidHom.id Lpr) (D.principalRealization f) (D.principalCharacter n, n) =
      f n • D.principalEvaluation n := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg, add_smul]
  | single m c =>
    by_cases h : m = n
    · subst m; simp
    · simp [h]

/-- The only coefficient family killed by the principal realization is a family
supported at zero. No condition on the radical of the skew form is needed. -/
theorem principalRealization_eq_zero_iff [Module.Free ℤ N] (f : D.unfrozen →₀ R) :
    D.principalRealization f = 0 ↔ f = Finsupp.single 0 (f 0) := by
  classical
  constructor
  · intro hf
    ext n
    by_cases hn : n = 0
    · subst n; simp
    · have he := congrArg
        (fun x => toFinsupp (AddMonoidHom.id Lpr) x (D.principalEmbedding n)) hf
      simp only [principalEmbedding_apply, principalRealization_coeff, map_zero,
        Finsupp.zero_apply] at he
      simpa [hn] using (D.smul_principalEvaluation_eq_zero_iff hn (f n)).mp he
  · intro hf
    rw [hf, principalRealization_single, principalField_zero, smul_zero]

/-- The nonzero-degree principal fields are linearly independent over arbitrary
commutative rational coefficient algebras. In particular, radical degrees survive. -/
theorem linearIndependent_principalField [Module.Free ℤ N] :
    LinearIndependent R (fun n : {n : D.unfrozen // n ≠ 0} =>
      D.principalField (R := R) n.val) := by
  rw [linearIndependent_iff]
  intro f hf
  let g := Finsupp.mapDomain (fun n : {n : D.unfrozen // n ≠ 0} => n.val) f
  have hg : D.principalRealization g = 0 := by
    dsimp only [g]
    rw [principalRealization, ← Finsupp.lmapDomain_apply (M := R) (R := R),
      ← LinearMap.comp_apply, Finsupp.linearCombination_comp_lmapDomain]
    exact hf
  have hg0 : g 0 = 0 := Finsupp.mapDomain_of_notMem_range f 0 (by simp)
  have hg' := (D.principalRealization_eq_zero_iff g).mp hg
  rw [hg0, Finsupp.single_zero] at hg'
  apply Finsupp.mapDomain_injective Subtype.val_injective
  simpa only [g, Finsupp.mapDomain_zero] using hg'

/-- Every allowed nonzero principal generator lies in the positive tropical
vertex algebra for the principal degree monoid. -/
theorem principalField_mem_tropicalVertexLieAlgebra (d : PositiveDegrees D.unfrozen)
    {n : D.unfrozen} (hn : n ∈ d.monoid) :
    D.principalField (R := R) n ∈
      tropicalVertexLieAlgebra (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) := by
  by_cases hn0 : n = 0
  · simp [hn0]
  · apply single_mem_tropicalVertexLieAlgebra
    · rw [principalEmbedding_apply]
      exact (d.mem_graph_monoid D.principalCharacter.toAddMonoidHom _ _).mpr ⟨hn, rfl⟩
    · exact fun h => hn0 (D.principalEmbedding_injective (h.trans (map_zero _).symm))
    · simpa only [principalEmbedding_apply, AddMonoidHom.id_apply, form_self, map_zero] using
        D.principalEvaluation_principalEmbedding (R := R) n n

/-- Principal realization sends finite coefficient families supported on the
positive monoid into its tropical vertex algebra. -/
theorem principalRealization_mem_tropicalVertexLieAlgebra (d : PositiveDegrees D.unfrozen)
    (f : D.unfrozen →₀ R) (hf : ∀ n ∈ f.support, n ∈ d.monoid) :
    D.principalRealization f ∈
      tropicalVertexLieAlgebra (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) := by
  classical
  rw [principalRealization, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ (fun n hn => Submodule.smul_mem _ _
    (D.principalField_mem_tropicalVertexLieAlgebra d (hf n hn)))

end Mei.SkewLatticeDatum
