/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal.Matching
public import Mei.Algebra.Category.AlgCat.Multispan.Span

/-!
# Theta sections of the focus-focus slab span

A matching section of the slab span is determined by its face value, and every element of the
slab algebra is the face value of exactly one section. The section `slabThetaSection t n b`
has face value the theta monomial `ϑ_{n,b}`, and its chamber values are the two Laurent images
of that monomial. The sections `ϑ_{n,b}` form a basis of the matching sections, indexed by
`ℤ × ℤ`, over every commutative ring and every smoothing parameter. The face-value map is an
algebra equivalence, so products of matching sections are products of their face values.

A linear family of matching sections realizes the actual weighted broken-line evaluations of
a finite list of incoming records, near a regular slab point, exactly when it is the
corresponding combination of theta sections. Products of theta sections are determined by the
formula `ϑ_{n,b} ϑ_{m,c} = t^r ∑_j (r choose j) ϑ_{n+m,b+c+j}`, with
`r = (|n| + |m| - |n + m|) / 2`; for instance `ϑ_{-1,0} ϑ_{1,0} = t ϑ_{0,0} + t ϑ_{0,1}`.

This is the normal form at one coefficient face: the global section on the punctured plane and
its completion are separate statements. The slab geometry follows Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AddMonoidAlgebra Mei.NodeAlgebra
  _root_.LaurentPolynomial

namespace Mei.FocusFocus

variable {R : Type*} [CommRing R] (t : R)

/-- The full-exponent slab correspondence as a multispan of algebras.
The false and true chamber indices denote its negative and positive sides. -/
abbrev slabTerminalAlgebraMultispan (t : R) :=
  MultispanIndex.ofAlgHoms (exponentLeftMap (C t * (1 + T 1)))
    (exponentRightMap (C t * (1 + T 1)))

/-- The algebra sections of the slab span are the semimodule sections of the underlying
span of linear maps. -/
def slabSectionsToSemimodule :=
  MultispanIndex.sectionsLinearEquivOfAlgHoms
    (exponentLeftMap (C t * (1 + T 1))) (exponentRightMap (C t * (1 + T 1)))

/-- Conversion from slab algebra sections to semimodule sections preserves face components. -/
@[simp]
theorem slabSectionsToSemimodule_apply_left (σ : AlgCat.sectionsSubalgebra
      (slabTerminalAlgebraMultispan t).multispan)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    (slabSectionsToSemimodule t σ).val (.left c) = σ.val (.left c) :=
  MultispanIndex.sectionsLinearEquivOfAlgHoms_apply_left _ _ σ c

/-- Conversion from slab algebra sections to semimodule sections preserves chamber components. -/
@[simp]
theorem slabSectionsToSemimodule_apply_right (σ : AlgCat.sectionsSubalgebra
      (slabTerminalAlgebraMultispan t).multispan) (side : Bool) :
    (slabSectionsToSemimodule t σ).val (.right side) = σ.val (.right side) :=
  MultispanIndex.sectionsLinearEquivOfAlgHoms_apply_right _ _ σ side

/-- Conversion from slab semimodule sections to algebra sections preserves chamber components. -/
@[simp]
theorem slabSectionsToSemimodule_symm_apply_right (σ : SemimoduleCat.sectionsSubmodule
      (slabTerminalMultispan t).multispan) (side : Bool) :
    ((slabSectionsToSemimodule t).symm σ).val (.right side) = σ.val (.right side) :=
  MultispanIndex.sectionsLinearEquivOfAlgHoms_symm_apply_right _ _ σ side

/-- Conversion from slab semimodule sections to algebra sections preserves face components. -/
@[simp]
theorem slabSectionsToSemimodule_symm_apply_left (σ : SemimoduleCat.sectionsSubmodule
      (slabTerminalMultispan t).multispan) (c : (MultispanShape.ofLinearOrder Bool).L) :
    ((slabSectionsToSemimodule t).symm σ).val (.left c) = σ.val (.left c) :=
  MultispanIndex.sectionsLinearEquivOfAlgHoms_symm_apply_left _ _ σ c

/-- The matching algebra sections of the slab span are algebra-equivalent to the slab algebra
by reading off the face value. -/
noncomputable def slabAlgebraEquiv :=
  MultispanIndex.sectionsAlgEquivOfAlgHoms (R := R)
    (exponentLeftMap (C t * (1 + T 1))) (exponentRightMap (C t * (1 + T 1)))

/-- The face value of a matching section is its image under `slabAlgebraEquiv`. -/
@[simp]
theorem slabAlgebraEquiv_apply (σ : AlgCat.sectionsSubalgebra
      (slabTerminalAlgebraMultispan t).multispan) :
    slabAlgebraEquiv t σ = σ.val (.left default) :=
  MultispanIndex.sectionsAlgEquivOfAlgHoms_apply _ _ σ

/-- The face component of a matching section reconstructed by `slabAlgebraEquiv`. -/
@[simp]
theorem slabAlgebraEquiv_symm_apply_left (z : TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)))
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    ((slabAlgebraEquiv t).symm z).val (.left c) = z :=
  MultispanIndex.sectionsAlgEquivOfAlgHoms_symm_apply_left _ _ z c

/-- The negative chamber value of a matching section reconstructed by `slabAlgebraEquiv` is the
left Laurent image of its face value. -/
@[simp]
theorem slabAlgebraEquiv_symm_apply_right_false
    (z : TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1))) :
    ((slabAlgebraEquiv t).symm z).val (.right false) =
      exponentLeftMap (C t * (1 + T 1)) z :=
  MultispanIndex.sectionsAlgEquivOfAlgHoms_symm_apply_right_false _ _ z

/-- The positive chamber value of a matching section reconstructed by `slabAlgebraEquiv` is the
right Laurent image of its face value. -/
@[simp]
theorem slabAlgebraEquiv_symm_apply_right_true
    (z : TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1))) :
    ((slabAlgebraEquiv t).symm z).val (.right true) =
      exponentRightMap (C t * (1 + T 1)) z :=
  MultispanIndex.sectionsAlgEquivOfAlgHoms_symm_apply_right_true _ _ z

/-- The matching sections of the slab span are linearly identified with the slab algebra by
reading off the face value. -/
abbrev slabSectionsEquiv : AlgCat.sectionsSubalgebra
    (slabTerminalAlgebraMultispan t).multispan ≃ₗ[R]
      TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)) :=
  (slabAlgebraEquiv t).toLinearEquiv

/-- The matching section of the slab span whose face value is the theta monomial `ϑ_{n,b}`. -/
def slabThetaSection (n b : ℤ) :
    AlgCat.sectionsSubalgebra (slabTerminalAlgebraMultispan t).multispan :=
  (slabAlgebraEquiv t).symm (theta t n b)

/-- The face component of the theta section `ϑ_{n,b}` is the theta monomial. -/
@[simp]
theorem slabThetaSection_left (n b : ℤ) (c : (MultispanShape.ofLinearOrder Bool).L) :
    (slabThetaSection t n b).val (.left c) = theta t n b :=
  slabAlgebraEquiv_symm_apply_left t (theta t n b) c

/-- The negative chamber value of `ϑ_{n,b}` is the left Laurent image of the monomial. -/
@[simp]
theorem slabThetaSection_right_false (n b : ℤ) :
    (slabThetaSection t n b).val (.right false) =
      exponentLeftMap (C t * (1 + T 1)) (theta t n b) :=
  slabAlgebraEquiv_symm_apply_right_false t (theta t n b)

/-- The positive chamber value of `ϑ_{n,b}` is the right Laurent image of the monomial. -/
@[simp]
theorem slabThetaSection_right_true (n b : ℤ) :
    (slabThetaSection t n b).val (.right true) =
      exponentRightMap (C t * (1 + T 1)) (theta t n b) :=
  slabAlgebraEquiv_symm_apply_right_true t (theta t n b)

/-- The theta sections form a basis of the matching sections of the slab span, indexed by
the exponents `(n, b)`. -/
def slabThetaSectionBasis : Module.Basis (ℤ × ℤ) R
    (AlgCat.sectionsSubalgebra (slabTerminalAlgebraMultispan t).multispan) :=
  (laurentBasis (C t * (1 + T 1))).map (slabSectionsEquiv t).symm

/-- The basis vector at `(n, b)` is the theta section `ϑ_{n,b}`. -/
@[simp]
theorem slabThetaSectionBasis_apply (n b : ℤ) :
    slabThetaSectionBasis t (n, b) = slabThetaSection t n b := by
  rw [slabThetaSectionBasis, Module.Basis.map_apply, laurentBasis_apply_eq_theta]
  rfl

/-- Scaling the theta section scales the face value. -/
theorem slabThetaSection_smul (c : R) (n b : ℤ) :
    c • slabThetaSection t n b =
      (slabAlgebraEquiv t).symm (c • theta t n b) :=
  (map_smul _ c _).symm

/-- The negative chamber value of a multiple of `ϑ_{n,b}` is the left Laurent image of the
multiple of the monomial. -/
theorem slabThetaSection_smul_right_false (c : R) (n b : ℤ) :
    (c • slabThetaSection t n b).val (.right false) =
      exponentLeftMap (C t * (1 + T 1)) (c • theta t n b) := by
  rw [slabThetaSection_smul]
  exact slabAlgebraEquiv_symm_apply_right_false t (c • theta t n b)

/-- The positive chamber value of a multiple of `ϑ_{n,b}` is the right Laurent image of the
multiple of the monomial. -/
theorem slabThetaSection_smul_right_true (c : R) (n b : ℤ) :
    (c • slabThetaSection t n b).val (.right true) =
      exponentRightMap (C t * (1 + T 1)) (c • theta t n b) := by
  rw [slabThetaSection_smul]
  exact slabAlgebraEquiv_symm_apply_right_true t (c • theta t n b)

/-- At a generic endpoint of the negative chamber, the actual weighted broken-line sum of the
incoming record `c ϑ_{n,b}` is the negative chamber value of the section `c • ϑ_{n,b}`. -/
theorem slabThetaSection_smul_right_false_eq_slabThetaEvaluation (c : R) (n b : ℤ)
    (Q : ℝ × ℝ) (hQ : Q.1 < 0)
    (hgeneric : Q.1 / (n : ℝ) < 0 → ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0) :
    (c • slabThetaSection t n b).val (.right false) = slabThetaEvaluation t c n b Q := by
  rw [slabThetaSection_smul_right_false,
    slabThetaEvaluation_eq_exponentLeftMap t c n b Q hQ hgeneric]

/-- At a generic endpoint of the positive chamber, the actual weighted broken-line sum of the
incoming record `c ϑ_{n,b}` is the positive chamber value of the section `c • ϑ_{n,b}`. -/
theorem slabThetaSection_smul_right_true_eq_slabThetaEvaluation (c : R) (n b : ℤ)
    (Q : ℝ × ℝ) (hQ : 0 < Q.1)
    (hgeneric : Q.1 / (n : ℝ) < 0 → ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0) :
    (c • slabThetaSection t n b).val (.right true) = slabThetaEvaluation t c n b Q := by
  rw [slabThetaSection_smul_right_true,
    slabThetaEvaluation_eq_exponentRightMap t c n b Q hQ hgeneric]

/-- The product of theta matching sections is
`t^r ∑_{j=0}^r (r choose j) ϑ_{n+m,b+c+j}`, where `r = (|n| + |m| - |n + m|) / 2`. -/
theorem slabThetaSection_mul (n m b c : ℤ) :
    slabThetaSection t n b * slabThetaSection t m c =
      t ^ ((n.natAbs + m.natAbs - (n + m).natAbs) / 2) •
        ∑ j ∈ Finset.range ((n.natAbs + m.natAbs - (n + m).natAbs) / 2 + 1),
          ((n.natAbs + m.natAbs - (n + m).natAbs) / 2).choose j •
            slabThetaSection t (n + m) (b + c + j) := by
  rw [slabThetaSection, slabThetaSection, ← map_mul, theta_mul_theta, map_smul,
    map_sum]
  simp only [map_nsmul, slabThetaSection]

/-- The check `ϑ_{-1,0} ϑ_{1,0} = t ϑ_{0,0} + t ϑ_{0,1}` for matching sections. -/
theorem slabThetaSection_neg_one_mul_thetaSection_one :
    slabThetaSection t (-1) 0 * slabThetaSection t 1 0 =
      t • slabThetaSection t 0 0 + t • slabThetaSection t 0 1 := by
  simp only [slabThetaSection, ← map_mul, theta_neg_one_mul_theta_one, map_add, map_smul]

section Coefficients

variable {ι H : Type*} [AddCommMonoid H] [Module R H]
  (s : Finset ι) (n b : ι → ℤ) (α : ι → H →ₗ[R] R)
  (h : TauCeti.Toric.IsIntegralLattice
    ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {v : ℝ} {L U : ℝ × ℝ}

/-- The combination of theta sections with the coefficients `α i a` is the section whose face
value is the common total theta lift. -/
theorem sum_smul_slabThetaSection (a : H) :
    ∑ i ∈ s, α i a • slabThetaSection t (n i) (b i) =
      (slabAlgebraEquiv t).symm (slabTerminalFiniteLift s n b t α a) := by
  rw [slabTerminalFiniteLift_apply, map_sum]
  simp only [map_smul, slabThetaSection]

/-- Normal form of the geometric matching families. A linear family of matching sections of
the slab span has the actual weighted broken-line sums of the incoming records `α i` as its
chamber values at two opposite-side endpoints of the common terminal neighborhood exactly when
it is the combination `a ↦ ∑ i, α i a • ϑ_{n i, b i}` of theta sections. -/
theorem slabTerminalFinite_matchingFamily_iff
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (ℓ : H →ₗ[R] AlgCat.sectionsSubalgebra (slabTerminalAlgebraMultispan t).multispan) :
    (∀ a (side : Bool), (ℓ a).val (.right side) =
      ∑ i ∈ s, (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) (if side then U else L)) ↔
      ∀ a, ℓ a = ∑ i ∈ s, α i a • slabThetaSection t (n i) (b i) := by
  constructor
  · intro hℓ a
    rw [sum_smul_slabThetaSection]
    apply (slabAlgebraEquiv t).injective
    rw [AlgEquiv.apply_symm_apply, slabAlgebraEquiv_apply]
    exact (slabSectionsToSemimodule_apply_left t (ℓ a) default).symm.trans
      (slabTerminalFinite_matchingFamily_face s n b t α h hL hU hLs hUs
        ((slabSectionsToSemimodule t).toLinearMap ∘ₗ ℓ) (by
          intro a side
          rw [LinearMap.comp_apply, LinearEquiv.coe_coe, slabSectionsToSemimodule_apply_right]
          exact hℓ a side) a default)
  · intro hℓ a side
    rw [hℓ a, sum_smul_slabThetaSection]
    cases side
    · rw [slabAlgebraEquiv_symm_apply_right_false]
      refine (exponentLeftMap_slabTerminalFiniteLift s n b t α hL hLs a).trans ?_
      simp only [slabThetaFamily_weightedEvaluation, Bool.false_eq_true, ↓reduceIte]
    · rw [slabAlgebraEquiv_symm_apply_right_true]
      refine (exponentRightMap_slabTerminalFiniteLift s n b t α hU hUs a).trans ?_
      simp only [slabThetaFamily_weightedEvaluation, ↓reduceIte]

end Coefficients

end Mei.FocusFocus
