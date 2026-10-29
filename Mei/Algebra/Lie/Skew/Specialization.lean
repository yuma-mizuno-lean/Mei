/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Skew.Ray
public import Mei.Algebra.Lie.BCH.RestrictScalars
public import Mei.RingTheory.PowerSeries.EulerDerivInv
public import Mei.RingTheory.PowerSeries.Log

/-!
# Coefficient specialization of skew Lie algebras

An algebra map carrying one alternating form to another induces a Lie map on
formal skew generators. It preserves positive support and the exponent grading,
including when specialization kills coefficients. Restricting scalars to the
common base ring makes this a graded Lie homomorphism, so the existing truncation
and completed BCH constructions apply to coefficient specializations.

The construction uses Mathlib's `Finsupp.mapRange.linearMap` on the coefficient
coordinates `SkewLieAlgebra.toFinsupp`; positive restriction follows
`LogarithmicVectorField.coefficientGradedLieHom`. The completed map uses
`GradedLieHom.completedMap` and `PositiveDegrees.completedBCHRestrictScalarsEquiv`.
It carries arbitrary ray exponentials and the normalized potentials
`eulerDerivInv (logOf f)` to those of the specialized scalar series.
The skew bracket convention is that of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1 and
Appendix B, arXiv:1411.1394v2.
-/

public section
noncomputable section

namespace Mei.SkewLieAlgebra

variable {K R S Γ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommGroup Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt)
  (γ : Γ →ₗ[ℤ] Γ →ₗ[ℤ] S) (hγ : γ.IsAlt)
  (φ : R →ₐ[K] S) (hφ : ∀ n m, φ (β n m) = γ n m)

private def coefficientLinearMap : SkewLieAlgebra β hβ →ₗ[K] SkewLieAlgebra γ hγ :=
  ((toFinsupp γ hγ).symm.toLinearMap.restrictScalars K).comp
    ((Finsupp.mapRange.linearMap φ.toLinearMap).comp
      ((toFinsupp β hβ).toLinearMap.restrictScalars K))

private theorem coefficientLinearMap_single (n : Γ) (r : R) :
    coefficientLinearMap β hβ γ hγ φ (single β hβ n r) = single γ hγ n (φ r) := by
  apply (toFinsupp γ hγ).injective
  simp [coefficientLinearMap, Finsupp.mapRange.linearMap_apply]

/-- Specialize coefficients of formal skew generators along a map preserving the form. -/
def coefficientMap : SkewLieAlgebra β hβ →ₗ⁅K⁆ SkewLieAlgebra γ hγ :=
  { coefficientLinearMap β hβ γ hγ φ with
    map_lie' := by
      intro x y
      simp only [LinearMap.toFun_eq_coe]
      induction x using induction_on β hβ with
      | h0 => simp
      | hs n r =>
        induction y using induction_on β hβ with
        | h0 => simp
        | hs m s => simp [single_bracket_single, coefficientLinearMap_single, hφ]
        | ha y z hy hz => simp_all
      | ha x z hx hz => simp_all }

/-- Specialization keeps the exponent and applies the coefficient homomorphism. -/
@[simp]
theorem coefficientMap_single (n : Γ) (r : R) :
    coefficientMap β hβ γ hγ φ hφ (single β hβ n r) = single γ hγ n (φ r) :=
  coefficientLinearMap_single β hβ γ hγ φ n r

/-- Each formal coefficient is specialized separately. -/
@[simp]
theorem toFinsupp_coefficientMap (x : SkewLieAlgebra β hβ) (n : Γ) :
    toFinsupp γ hγ (coefficientMap β hβ γ hγ φ hφ x) n = φ (toFinsupp β hβ x n) := by
  induction x using induction_on β hβ with
  | h0 => simp
  | hs m r =>
    rw [coefficientMap_single]
    by_cases h : m = n <;> simp [h]
  | ha x y hx hy => simp [hx, hy]

/-- Identity coefficients induce the identity Lie map. -/
@[simp]
theorem coefficientMap_id :
    coefficientMap β hβ β hβ (AlgHom.id K R) (fun _ _ => by simp) = LieHom.id := by
  apply LieHom.ext
  intro x
  apply SkewLieAlgebra.ext
  intro n
  rw [toFinsupp_coefficientMap]
  rfl

/-- Coefficient specialization is functorial. -/
@[simp]
theorem coefficientMap_comp {T : Type*} [CommRing T] [Algebra K T]
    (δ : Γ →ₗ[ℤ] Γ →ₗ[ℤ] T) (hδ : δ.IsAlt)
    (ψ : S →ₐ[K] T) (hψ : ∀ n m, ψ (γ n m) = δ n m) :
    (coefficientMap γ hγ δ hδ ψ hψ).comp (coefficientMap β hβ γ hγ φ hφ) =
      coefficientMap β hβ δ hδ (ψ.comp φ) (fun n m => by simp [hφ, hψ]) := by
  ext x n
  simp

/-- Coefficient specialization cannot introduce an exponent outside positive support. -/
theorem coefficientMap_mem_positiveLieAlgebra (d : PositiveDegrees Γ)
    {x : SkewLieAlgebra β hβ} (hx : x ∈ positiveLieAlgebra β hβ d) :
    coefficientMap β hβ γ hγ φ hφ x ∈ positiveLieAlgebra γ hγ d := by
  rw [mem_positiveLieAlgebra_iff] at hx ⊢
  intro n hn
  simp [hx n hn]

/-- Coefficient specialization on the positive skew algebra, retaining its degree
and cutoff and restricting scalars to the common base ring. -/
def coefficientGradedLieHom (d : PositiveDegrees Γ) :
    GradedLieHom (PositiveDegreeMap.id d)
      (fun n => (positiveGrading β hβ d n).restrictScalars K)
      (fun n => (positiveGrading γ hγ d n).restrictScalars K) where
  toLieHom :=
    { toLinearMap :=
        ((coefficientMap β hβ γ hγ φ hφ).toLinearMap.comp
          ((positiveLieAlgebra β hβ d).incl.toLinearMap.restrictScalars K)).codRestrict
          ((positiveLieAlgebra γ hγ d).toSubmodule.restrictScalars K)
          (fun x => coefficientMap_mem_positiveLieAlgebra β hβ γ hγ φ hφ d x.property)
      map_lie' := by
        intro x y
        exact Subtype.ext ((coefficientMap β hβ γ hγ φ hφ).map_lie x.val y.val) }
  map_mem {n x} hx := by
    simp only [Submodule.restrictScalars_mem, mem_positiveGrading_iff] at hx
    simp only [PositiveDegreeMap.id_apply, Submodule.restrictScalars_mem,
      mem_positiveGrading_iff]
    obtain ⟨r, hr⟩ := (mem_grade_iff β hβ n x.val).mp hx
    exact (mem_grade_iff γ hγ n _).mpr
      ⟨φ r, (coefficientMap_single β hβ γ hγ φ hφ n r).symm.trans
        (congrArg (coefficientMap β hβ γ hγ φ hφ) hr)⟩

/-- Forgetting positive support recovers the ambient coefficient map. -/
@[simp]
theorem coe_coefficientGradedLieHom (d : PositiveDegrees Γ)
    (x : positiveLieAlgebra β hβ d) :
    (coefficientGradedLieHom β hβ γ hγ φ hφ d x).val =
      coefficientMap β hβ γ hγ φ hφ x.val := (rfl)

/-- The positive specialization of identity coefficients is the identity graded map. -/
@[simp]
theorem coefficientGradedLieHom_id (d : PositiveDegrees Γ) :
    coefficientGradedLieHom β hβ β hβ (AlgHom.id K R) (fun _ _ => by simp) d =
      GradedLieHom.id (fun n => (positiveGrading β hβ d n).restrictScalars K) := by
  apply GradedLieHom.ext
  intro x
  apply Subtype.ext
  simp only [coe_coefficientGradedLieHom, coefficientMap_id, LieHom.id_apply,
    GradedLieHom.id_apply]

/-- Positive coefficient specializations compose on the same exponent grading. -/
@[simp]
theorem coefficientGradedLieHom_comp {T : Type*} [CommRing T] [Algebra K T]
    (δ : Γ →ₗ[ℤ] Γ →ₗ[ℤ] T) (hδ : δ.IsAlt)
    (ψ : S →ₐ[K] T) (hψ : ∀ n m, ψ (γ n m) = δ n m) (d : PositiveDegrees Γ) :
    (coefficientGradedLieHom γ hγ δ hδ ψ hψ d).toLieHom.comp
        (coefficientGradedLieHom β hβ γ hγ φ hφ d).toLieHom =
      (coefficientGradedLieHom β hβ δ hδ (ψ.comp φ)
        (fun n m => by simp [hφ, hψ]) d).toLieHom := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (coefficientMap_comp β hβ γ hγ φ hφ δ hδ ψ hψ) x.val

section Ray

variable {d : PositiveDegrees Γ} {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

/-- Coefficient specialization of a homogeneous ray generator. -/
@[simp]
theorem coefficientGradedLieHom_rayGenerator (j : ℕ) (c : R) :
    coefficientGradedLieHom β hβ γ hγ φ hφ d (rayGenerator β hβ hn hn0 j c) =
      rayGenerator γ hγ hn hn0 j (φ c) := by
  apply Subtype.ext
  simp

/-- Specialization of a finite ray potential is coefficientwise. -/
theorem coefficientGradedLieHom_rayPartialSum (k : ℕ) (f : PowerSeries R) :
    coefficientGradedLieHom β hβ γ hγ φ hφ d (rayPartialSum β hβ hn hn0 k f) =
      rayPartialSum γ hγ hn hn0 k (PowerSeries.map φ.toRingHom f) := by
  classical
  simp [rayPartialSum_apply]

end Ray

variable [DecidableEq Γ] (d : PositiveDegrees Γ)

local notation "ℒR" => positiveGrading β hβ d
local notation "ℒS" => positiveGrading γ hγ d

/-- Coefficient specialization on finite Lie truncations, expressed over the
common scalar ring and on the original quotient carriers. -/
def coefficientTruncatedMap (k : ℕ) :
    d.truncatedLie ℒR k →ₗ⁅K⁆ d.truncatedLie ℒS k :=
  (d.truncatedRestrictScalarsEquiv (R := K) ℒS k).toLieHom.comp
    (((coefficientGradedLieHom β hβ γ hγ φ hφ d).truncatedMap k (by simp)).comp
      (d.truncatedRestrictScalarsEquiv (R := K) ℒR k).symm.toLieHom)

/-- Finite specialization is computed on representatives by the positive Lie map. -/
@[simp]
theorem coefficientTruncatedMap_mk (k : ℕ) (x : positiveLieAlgebra β hβ d) :
    coefficientTruncatedMap β hβ γ hγ φ hφ d k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (coefficientGradedLieHom β hβ γ hγ φ hφ d x) := by
  simp [coefficientTruncatedMap, GradedLieHom.truncatedMap_mk]

/-- Finite coefficient specializations compose on the original Lie quotient carriers. -/
@[simp]
theorem coefficientTruncatedMap_comp {T : Type*} [CommRing T] [Algebra K T]
    (δ : Γ →ₗ[ℤ] Γ →ₗ[ℤ] T) (hδ : δ.IsAlt)
    (ψ : S →ₐ[K] T) (hψ : ∀ n m, ψ (γ n m) = δ n m) (k : ℕ) :
    (coefficientTruncatedMap γ hγ δ hδ ψ hψ d k).comp
        (coefficientTruncatedMap β hβ γ hγ φ hφ d k) =
      coefficientTruncatedMap β hβ δ hδ (ψ.comp φ)
        (fun n m => by simp [hφ, hψ]) d k := by
  apply LieHom.ext
  intro y
  induction y using Submodule.Quotient.induction_on with | _ x
  simp only [LieHom.comp_apply, coefficientTruncatedMap_mk]
  congr 1
  exact DFunLike.congr_fun
    (coefficientGradedLieHom_comp β hβ γ hγ φ hφ δ hδ ψ hψ d) x

end Mei.SkewLieAlgebra

universe u v

namespace Mei.SkewLieAlgebra

variable {R S : Type u} {Γ : Type v} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [AddCommGroup Γ] [DecidableEq Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt)
  (γ : Γ →ₗ[ℤ] Γ →ₗ[ℤ] S) (hγ : γ.IsAlt)
  (φ : R →ₐ[ℚ] S) (hφ : ∀ n m, φ (β n m) = γ n m) (d : PositiveDegrees Γ)

local notation "ℒR" => positiveGrading β hβ d
local notation "ℒS" => positiveGrading γ hγ d

/-- Specialize a completed skew label, using the canonical comparisons with
rational scalar restriction on both sides. -/
def coefficientCompletedMap : d.completedBCHGroup ℒR →* d.completedBCHGroup ℒS :=
  (d.completedBCHRestrictScalarsEquiv (R := ℚ) ℒS).toMonoidHom.comp
    (((coefficientGradedLieHom β hβ γ hγ φ hφ d).completedMap).comp
      (d.completedBCHRestrictScalarsEquiv (R := ℚ) ℒR).symm.toMonoidHom)

/-- Specialization at every cutoff is the BCH map of finite Lie specialization. -/
@[simp]
theorem projection_coefficientCompletedMap (k : ℕ) (g : d.completedBCHGroup ℒR) :
    CompletedGroup.projection k (coefficientCompletedMap β hβ γ hγ φ hφ d g) =
      (coefficientTruncatedMap β hβ γ hγ φ hφ d k).bchGroupMap
        (CompletedGroup.projection k g) := by
  simp only [coefficientCompletedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv,
    GradedLieHom.projection_completedMap_of_le
      (coefficientGradedLieHom β hβ γ hγ φ hφ d) k (a := k) (by simp),
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv_symm,
    LieHom.bchGroupMap_exp]
  -- The projection has a categorical tower-object type. Re-elaborate the RHS
  -- with the concrete quotient before rewriting it as an exponential.
  change BCHGroup.exp _ =
    (coefficientTruncatedMap β hβ γ hγ φ hφ d k).bchGroupMap
      (CompletedGroup.projection k g : BCHGroup (d.truncatedLie ℒR k))
  rw [← BCHGroup.exp_log (CompletedGroup.projection k g : BCHGroup (d.truncatedLie ℒR k)),
    LieHom.bchGroupMap_exp]
  congr 1
  simp [coefficientTruncatedMap]

/-- Coefficient specialization preserves exponentiation of finite positive Lie elements. -/
@[simp]
theorem coefficientCompletedMap_expToCompletion (x : positiveLieAlgebra β hβ d) :
    coefficientCompletedMap β hβ γ hγ φ hφ d (d.expToCompletion ℒR x) =
      d.expToCompletion ℒS (coefficientGradedLieHom β hβ γ hγ φ hφ d x) := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_coefficientCompletedMap, PositiveDegrees.projection_expToCompletion,
    LieHom.bchGroupMap_exp, LieIdeal.mkQ_apply, coefficientTruncatedMap_mk]
  rfl

/-- Identity coefficients act identically on completed skew labels. -/
@[simp]
theorem coefficientCompletedMap_id :
    coefficientCompletedMap β hβ β hβ (AlgHom.id ℚ R) (fun _ _ => by simp) d =
      MonoidHom.id (d.completedBCHGroup ℒR) := by
  ext g : 1
  simp [coefficientCompletedMap]

/-- Completed coefficient specialization respects composition. -/
@[simp]
theorem coefficientCompletedMap_comp {T : Type u} [CommRing T] [Algebra ℚ T]
    (δ : Γ →ₗ[ℤ] Γ →ₗ[ℤ] T) (hδ : δ.IsAlt)
    (ψ : S →ₐ[ℚ] T) (hψ : ∀ n m, ψ (γ n m) = δ n m) :
    (coefficientCompletedMap γ hγ δ hδ ψ hψ d).comp
        (coefficientCompletedMap β hβ γ hγ φ hφ d) =
      coefficientCompletedMap β hβ δ hδ (ψ.comp φ)
        (fun n m => by simp [hφ, hψ]) d := by
  ext g : 1
  apply CompletedGroup.ext
  intro k
  simp only [MonoidHom.comp_apply, projection_coefficientCompletedMap]
  -- Re-express the categorical projection as its concrete BCH quotient.
  generalize (CompletedGroup.projection k g : BCHGroup (d.truncatedLie ℒR k)) = x
  rw [← BCHGroup.exp_log x]
  simp only [LieHom.bchGroupMap_exp]
  congr 1
  exact DFunLike.congr_fun
    (coefficientTruncatedMap_comp β hβ γ hγ φ hφ d δ hδ ψ hψ k) (BCHGroup.log x)

variable {d} {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

/-- Specialize an arbitrary completed ray exponential by specializing its scalar series. -/
@[simp]
theorem coefficientCompletedMap_rayExp (f : PowerSeries R) :
    coefficientCompletedMap β hβ γ hγ φ hφ d (rayExp β hβ hn hn0 f) =
      rayExp γ hγ hn hn0 (PowerSeries.map φ.toRingHom f) := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_coefficientCompletedMap, projection_rayExp, LieHom.bchGroupMap_exp,
    LieIdeal.mkQ_apply, coefficientTruncatedMap_mk,
    coefficientGradedLieHom_rayPartialSum]
  rfl

/-- The normalized wall label of a constant-one ray function specializes to the
normalized label of the specialized function. Rational normalizations are retained,
including when coefficients vanish after specialization. -/
theorem coefficientCompletedMap_rayExp_eulerDerivInv_logOf (f : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 1) (c : ℚ) :
    coefficientCompletedMap β hβ γ hγ φ hφ d
        (rayExp β hβ hn hn0 ((algebraMap ℚ R c) • PowerSeries.eulerDerivInv
          (PowerSeries.logOf f))) =
      rayExp γ hγ hn hn0 ((algebraMap ℚ S c) • PowerSeries.eulerDerivInv
        (PowerSeries.logOf (PowerSeries.map φ.toRingHom f))) := by
  rw [coefficientCompletedMap_rayExp]
  congr 1
  have hs (a : PowerSeries R) :
      PowerSeries.map φ.toRingHom ((algebraMap ℚ R c) • a) =
        (algebraMap ℚ S c) • PowerSeries.map φ.toRingHom a := by
    ext j
    simp
  rw [hs, PowerSeries.map_eulerDerivInv, PowerSeries.map_logOf φ.toRingHom f hf]

end Mei.SkewLieAlgebra
