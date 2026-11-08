/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal.Matching

/-!
# Theta sections of the focus-focus slab span

A matching section of the slab span is determined by its face value, and every element of the
slab algebra is the face value of exactly one section. The section `slabThetaSection t n b`
has face value the theta monomial `ϑ_{n,b}`, and its chamber values are the two Laurent images
of that monomial. The sections `ϑ_{n,b}` form a basis of the matching sections, indexed by
`ℤ × ℤ`, over every commutative ring and every smoothing parameter.

A linear family of matching sections realizes the actual weighted broken-line evaluations of
a finite list of incoming records, near a regular slab point, exactly when it is the
corresponding combination of theta sections. The sections whose chamber values are the pointwise
products of two theta sections are determined by the product formula
`ϑ_{n,b} ϑ_{m,c} = t^r ∑_j (r choose j) ϑ_{n+m,b+c+j}`, with `r = (|n| + |m| - |n + m|) / 2`;
for instance `ϑ_{-1,0} ϑ_{1,0} = t ϑ_{0,0} + t ϑ_{0,1}`.

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

/-- The matching sections of the slab span are identified with the slab algebra by reading
off the face value. -/
abbrev slabSectionsEquiv :
    SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan ≃ₗ[R]
      TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)) :=
  MultispanIndex.sectionsLinearEquivOfLinearMaps _ _

/-- The matching section of the slab span whose face value is the theta monomial `ϑ_{n,b}`. -/
def slabThetaSection (n b : ℤ) :
    SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan :=
  (slabSectionsEquiv t).symm (theta t n b)

/-- The theta section is the section with the theta monomial as face value. -/
theorem slabThetaSection_def (n b : ℤ) :
    slabThetaSection t n b = (slabSectionsEquiv t).symm (theta t n b) := (rfl)

/-- The face component of the theta section `ϑ_{n,b}` is the theta monomial. -/
@[simp]
theorem slabThetaSection_left (n b : ℤ) (c : (MultispanShape.ofLinearOrder Bool).L) :
    (slabThetaSection t n b).val (.left c) = theta t n b :=
  MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_left _ _ _ c

/-- The negative chamber value of `ϑ_{n,b}` is the left Laurent image of the monomial. -/
@[simp]
theorem slabThetaSection_right_false (n b : ℤ) :
    (slabThetaSection t n b).val (.right false) =
      exponentLeftMap (C t * (1 + T 1)) (theta t n b) :=
  MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_false _ _ _

/-- The positive chamber value of `ϑ_{n,b}` is the right Laurent image of the monomial. -/
@[simp]
theorem slabThetaSection_right_true (n b : ℤ) :
    (slabThetaSection t n b).val (.right true) =
      exponentRightMap (C t * (1 + T 1)) (theta t n b) :=
  MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_true _ _ _

/-- The theta sections form a basis of the matching sections of the slab span, indexed by
the exponents `(n, b)`. -/
def slabThetaSectionBasis : Module.Basis (ℤ × ℤ) R
    (SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan) :=
  (laurentBasis (C t * (1 + T 1))).map (slabSectionsEquiv t).symm

/-- The basis vector at `(n, b)` is the theta section `ϑ_{n,b}`. -/
@[simp]
theorem slabThetaSectionBasis_apply (n b : ℤ) :
    slabThetaSectionBasis t (n, b) = slabThetaSection t n b := by
  rw [slabThetaSectionBasis, Module.Basis.map_apply, laurentBasis_apply_eq_theta,
    slabThetaSection_def]

/-- Scaling the theta section scales the face value. -/
theorem slabThetaSection_smul (c : R) (n b : ℤ) :
    c • slabThetaSection t n b =
      (slabSectionsEquiv t).symm (c • theta t n b) :=
  (map_smul _ c _).symm

/-- The negative chamber value of a multiple of `ϑ_{n,b}` is the left Laurent image of the
multiple of the monomial. -/
theorem slabThetaSection_smul_right_false (c : R) (n b : ℤ) :
    (c • slabThetaSection t n b).val (.right false) =
      exponentLeftMap (C t * (1 + T 1)) (c • theta t n b) := by
  rw [slabThetaSection_smul]
  exact MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_false _ _ _

/-- The positive chamber value of a multiple of `ϑ_{n,b}` is the right Laurent image of the
multiple of the monomial. -/
theorem slabThetaSection_smul_right_true (c : R) (n b : ℤ) :
    (c • slabThetaSection t n b).val (.right true) =
      exponentRightMap (C t * (1 + T 1)) (c • theta t n b) := by
  rw [slabThetaSection_smul]
  exact MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_true _ _ _

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

/-- A matching section has as chamber values the products of the chamber values of
`ϑ_{n,b}` and `ϑ_{m,c}` exactly when it is
`t^r ∑_{j=0}^r (r choose j) ϑ_{n+m,b+c+j}`, where `r = (|n| + |m| - |n + m|) / 2`. -/
theorem slabThetaSection_chamber_mul_iff (n m b c : ℤ)
    (σ : SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan) :
    ((σ.val (.right false) : R[ℤ × ℤ]) =
        exponentLeftMap (C t * (1 + T 1)) (theta t n b) *
          exponentLeftMap (C t * (1 + T 1)) (theta t m c) ∧
      (σ.val (.right true) : R[ℤ × ℤ]) =
        exponentRightMap (C t * (1 + T 1)) (theta t n b) *
          exponentRightMap (C t * (1 + T 1)) (theta t m c)) ↔
      σ = t ^ ((n.natAbs + m.natAbs - (n + m).natAbs) / 2) •
        ∑ j ∈ Finset.range ((n.natAbs + m.natAbs - (n + m).natAbs) / 2 + 1),
          ((n.natAbs + m.natAbs - (n + m).natAbs) / 2).choose j •
            slabThetaSection t (n + m) (b + c + j) := by
  have hsum : (t ^ ((n.natAbs + m.natAbs - (n + m).natAbs) / 2) •
        ∑ j ∈ Finset.range ((n.natAbs + m.natAbs - (n + m).natAbs) / 2 + 1),
          ((n.natAbs + m.natAbs - (n + m).natAbs) / 2).choose j •
            slabThetaSection t (n + m) (b + c + j)) =
      (slabSectionsEquiv t).symm (theta t n b * theta t m c) := by
    rw [theta_mul_theta, map_smul, map_sum]
    simp only [map_nsmul, slabThetaSection_def]
  obtain ⟨z, rfl⟩ := (slabSectionsEquiv t).symm.surjective σ
  rw [hsum, (slabSectionsEquiv t).symm.injective.eq_iff]
  simp only [MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_false,
    MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_true,
    AlgHom.toLinearMap_apply, ← map_mul]
  exact ⟨fun h => exponentMaps_jointly_injective _ (Prod.ext h.1 h.2),
    fun h => ⟨congrArg _ h, congrArg _ h⟩⟩

/-- The Check `ϑ_{-1,0} ϑ_{1,0} = t ϑ_{0,0} + t ϑ_{0,1}` for matching sections: the section
with the products of the chamber values of `ϑ_{-1,0}` and `ϑ_{1,0}` is `t ϑ_{0,0} + t ϑ_{0,1}`. -/
theorem slabThetaSection_chamber_neg_one_mul_one_iff
    (σ : SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan) :
    ((σ.val (.right false) : R[ℤ × ℤ]) =
        exponentLeftMap (C t * (1 + T 1)) (theta t (-1) 0) *
          exponentLeftMap (C t * (1 + T 1)) (theta t 1 0) ∧
      (σ.val (.right true) : R[ℤ × ℤ]) =
        exponentRightMap (C t * (1 + T 1)) (theta t (-1) 0) *
          exponentRightMap (C t * (1 + T 1)) (theta t 1 0)) ↔
      σ = t • slabThetaSection t 0 0 + t • slabThetaSection t 0 1 := by
  rw [slabThetaSection_chamber_mul_iff]
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
      (slabSectionsEquiv t).symm (slabTerminalFiniteLift s n b t α a) := by
  rw [slabTerminalFiniteLift_apply, map_sum]
  simp only [map_smul, slabThetaSection_def]

/-- Normal form of the geometric matching families. A linear family of matching sections of
the slab span has the actual weighted broken-line sums of the incoming records `α i` as its
chamber values at two opposite-side endpoints of the common terminal neighborhood exactly when
it is the combination `a ↦ ∑ i, α i a • ϑ_{n i, b i}` of theta sections. -/
theorem slabTerminalFinite_matchingFamily_iff
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (ℓ : H →ₗ[R] SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan) :
    (∀ a (side : Bool), (ℓ a).val (.right side) =
      ∑ i ∈ s, (slabThetaFamily t (α i a) (n i) (b i) h).weightedEvaluation
          (slabThetaChartWeight t (α i a) (n i) (b i)) (if side then U else L)) ↔
      ∀ a, ℓ a = ∑ i ∈ s, α i a • slabThetaSection t (n i) (b i) := by
  constructor
  · intro hℓ a
    rw [sum_smul_slabThetaSection, LinearEquiv.eq_symm_apply]
    exact (MultispanIndex.sectionsLinearEquivOfLinearMaps_apply _ _ _).trans
      (slabTerminalFinite_matchingFamily_face s n b t α h hL hU hLs hUs ℓ hℓ a default)
  · intro hℓ a side
    rw [hℓ a, sum_smul_slabThetaSection]
    cases side
    · rw [MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_false]
      refine (exponentLeftMap_slabTerminalFiniteLift s n b t α hL hLs a).trans ?_
      simp only [slabThetaFamily_weightedEvaluation, Bool.false_eq_true, ↓reduceIte]
    · rw [MultispanIndex.sectionsLinearEquivOfLinearMaps_symm_apply_right_true]
      refine (exponentRightMap_slabTerminalFiniteLift s n b t α hU hUs a).trans ?_
      simp only [slabThetaFamily_weightedEvaluation, ↓reduceIte]

end Coefficients

end Mei.FocusFocus
