/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal.Matching
public import Mei.CategoryTheory.Limits.AlgebraMultispan

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
abbrev slabTerminalAlgebraMultispan (t : R) :
    MultispanIndex (MultispanShape.ofLinearOrder Bool) (AlgCat R) where
  left _ := AlgCat.of R (TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)))
  right _ := AlgCat.of R R[ℤ × ℤ]
  fst _ := AlgCat.ofHom (exponentLeftMap (C t * (1 + T 1)))
  snd _ := AlgCat.ofHom (exponentRightMap (C t * (1 + T 1)))

/-- The matching algebra sections of the slab span are algebra-equivalent to the slab algebra
by reading off the face value. -/
noncomputable def slabAlgebraEquiv : AlgCat.sectionsSubalgebra
    (slabTerminalAlgebraMultispan t).multispan ≃ₐ[R]
      TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)) := by
  let I := slabTerminalAlgebraMultispan t
  let hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom) := fun _ =>
    exponentMaps_jointly_injective (C t * (1 + T 1))
  let e := I.sectionsAlgEquivCompatibleFamilies hinj
  let family : TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)) →
      I.compatibleAlgebraFamilies := fun z => ⟨fun b => match b with
    | false => exponentLeftMap (C t * (1 + T 1)) z
    | true => exponentRightMap (C t * (1 + T 1)) z,
    (MultispanIndex.mem_compatibleAlgebraFamilies I _).mpr (fun a => ⟨z, by
      obtain rfl : a = default := Subsingleton.elim _ _
      exact Prod.ext rfl rfl⟩)⟩
  exact {
    toFun := fun s => s.val (.left default)
    invFun := fun z => e.symm (family z)
    left_inv := by
      intro x
      apply Subtype.ext
      funext j
      cases j with
      | left c =>
          obtain rfl : c = default := Subsingleton.elim _ _
          exact (I.sectionsAlgEquivCompatibleFamilies_symm_apply_left_iff hinj
            (family (x.val (.left default))) default _).mpr ⟨rfl, rfl⟩
      | right b =>
          exact (I.sectionsAlgEquivCompatibleFamilies_symm_apply_right hinj
            (family (x.val (.left default))) b).trans (by
            cases b
            · exact x.property (.fst default)
            · exact x.property (.snd default))
    right_inv := by
      intro z
      exact (I.sectionsAlgEquivCompatibleFamilies_symm_apply_left_iff hinj
        (family z) default z).mpr ⟨rfl, rfl⟩
    map_mul' := by intro x y; rfl
    map_add' := by intro x y; rfl
    commutes' := by intro r; rfl }

/-- The face value of a matching section is its image under `slabAlgebraEquiv`. -/
@[simp]
theorem slabAlgebraEquiv_apply (σ : AlgCat.sectionsSubalgebra
      (slabTerminalAlgebraMultispan t).multispan) :
    slabAlgebraEquiv t σ = σ.val (.left default) := by
  rw [slabAlgebraEquiv]
  rfl

/-- The face component of a matching section reconstructed by `slabAlgebraEquiv`. -/
@[simp]
theorem slabAlgebraEquiv_symm_apply_left (z : TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)))
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    ((slabAlgebraEquiv t).symm z).val (.left c) = z := by
  obtain rfl : c = default := Subsingleton.elim _ _
  exact slabAlgebraEquiv_apply t _ |>.symm.trans ((slabAlgebraEquiv t).apply_symm_apply z)

/-- The chamber value of a matching section reconstructed by `slabAlgebraEquiv` is the
corresponding Laurent image of its face value. -/
@[simp]
theorem slabAlgebraEquiv_symm_apply_right (z : TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)))
    (b : (MultispanShape.ofLinearOrder Bool).R) :
    ((slabAlgebraEquiv t).symm z).val (.right b) =
      match b with
      | false => exponentLeftMap (C t * (1 + T 1)) z
      | true => exponentRightMap (C t * (1 + T 1)) z := by
  rw [slabAlgebraEquiv]
  exact (slabTerminalAlgebraMultispan t).sectionsAlgEquivCompatibleFamilies_symm_apply_right
    (fun _ => exponentMaps_jointly_injective (C t * (1 + T 1))) _ _

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

/-- The theta section is the section with the theta monomial as face value. -/
theorem slabThetaSection_def (n b : ℤ) :
    slabThetaSection t n b = (slabAlgebraEquiv t).symm (theta t n b) := by
  rw [slabThetaSection]

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
  slabAlgebraEquiv_symm_apply_right t (theta t n b) false

/-- The positive chamber value of `ϑ_{n,b}` is the right Laurent image of the monomial. -/
@[simp]
theorem slabThetaSection_right_true (n b : ℤ) :
    (slabThetaSection t n b).val (.right true) =
      exponentRightMap (C t * (1 + T 1)) (theta t n b) :=
  slabAlgebraEquiv_symm_apply_right t (theta t n b) true

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
  exact slabThetaSection_def t n b

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
  exact slabAlgebraEquiv_symm_apply_right t (c • theta t n b) _

/-- The positive chamber value of a multiple of `ϑ_{n,b}` is the right Laurent image of the
multiple of the monomial. -/
theorem slabThetaSection_smul_right_true (c : R) (n b : ℤ) :
    (c • slabThetaSection t n b).val (.right true) =
      exponentRightMap (C t * (1 + T 1)) (c • theta t n b) := by
  rw [slabThetaSection_smul]
  exact slabAlgebraEquiv_symm_apply_right t (c • theta t n b) _

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
  change (slabAlgebraEquiv t).symm (theta t n b) * (slabAlgebraEquiv t).symm (theta t m c) = _
  rw [← map_mul, theta_mul_theta, map_smul, map_sum]
  simp only [map_nsmul, slabThetaSection_def]

/-- The check `ϑ_{-1,0} ϑ_{1,0} = t ϑ_{0,0} + t ϑ_{0,1}` for matching sections. -/
theorem slabThetaSection_neg_one_mul_one :
    slabThetaSection t (-1) 0 * slabThetaSection t 1 0 =
      t • slabThetaSection t 0 0 + t • slabThetaSection t 0 1 := by
  rw [slabThetaSection_mul]
  norm_num [Finset.sum_range_succ]

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
  simp only [map_smul, slabThetaSection_def]

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
    apply exponentMaps_jointly_injective (C t * (1 + T 1))
    refine Prod.ext ?_ ?_
    · have hleft := ((ℓ a).property (.fst default)).trans
        (congrArg (fun side : Bool => (ℓ a).val (.right side))
          (MultispanShape.ofLinearOrder_bool_fst default))
      have hvalueL : (ℓ a).val (.right false) =
          ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) L := by
        simpa only [Bool.false_eq_true, ↓reduceIte,
          slabThetaFamily_weightedEvaluation] using hℓ a false
      exact (hleft.trans hvalueL).trans
        (exponentLeftMap_slabTerminalFiniteLift s n b t α hL hLs a).symm
    · have hright := ((ℓ a).property (.snd default)).trans
        (congrArg (fun side : Bool => (ℓ a).val (.right side))
          (MultispanShape.ofLinearOrder_bool_snd default))
      have hvalueR : (ℓ a).val (.right true) =
          ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) U := by
        simpa only [↓reduceIte, slabThetaFamily_weightedEvaluation] using hℓ a true
      exact (hright.trans hvalueR).trans
        (exponentRightMap_slabTerminalFiniteLift s n b t α hU hUs a).symm
  · intro hℓ a side
    rw [hℓ a, sum_smul_slabThetaSection]
    cases side
    · rw [slabAlgebraEquiv_symm_apply_right t _ false]
      refine (exponentLeftMap_slabTerminalFiniteLift s n b t α hL hLs a).trans ?_
      simp only [slabThetaFamily_weightedEvaluation, Bool.false_eq_true, ↓reduceIte]
    · rw [slabAlgebraEquiv_symm_apply_right t _ true]
      refine (exponentRightMap_slabTerminalFiniteLift s n b t α hU hUs a).trans ?_
      simp only [slabThetaFamily_weightedEvaluation, ↓reduceIte]

end Coefficients

end Mei.FocusFocus
