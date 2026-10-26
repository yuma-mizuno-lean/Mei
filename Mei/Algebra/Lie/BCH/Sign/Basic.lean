/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Sign
public import Mei.Algebra.Lie.BCH.Completion
public import Mei.Algebra.Lie.Graded.Truncation.Transition
public import Mei.Algebra.Lie.BCH.Subgroup
import Mei.Algebra.Group.Hom.Bijective

/-!
# Sign factorization of truncated BCH groups

Every element of a finite degree truncation has a unique ordered factorization
into the positive, zero and negative sign subgroups. The factors are functions
of the product and commute with lowering the cutoff. These are set equivalences:
recombination is generally not a group homomorphism.

This formalizes the finite-order (truncated) form of the sign factorization in Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.2, equation (5)
([arXiv:1603.00416v4](https://arxiv.org/pdf/1603.00416v4)). The completed form is
proved in `Mei.Algebra.Lie.BCH.Sign.Completion`.

The proof uses `Mei.signDecomposition` and the central successive kernels of
`Mei.PositiveDegrees.truncationMap`. Central corrections make the nonlinear BCH
recombination act by translation on each new kernel. No freeness, finite rank,
finite generation of the positive monoid, or nilpotence of the original Lie
algebra is required.
-/

public section

noncomputable section

namespace Mei

open BCHGroup

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  (ℒ : N → Submodule R L) (θ : N →+ A)

section Product

variable [SetLike.GradedBracket ℒ ℒ] [LieRing.IsNilpotent L]

/-- Recombine one element of each sign subgroup, in positive-zero-negative order. -/
def signProduct (a : ∀ s, (signSubalgebra ℒ θ s).bchSubgroup) : BCHGroup L :=
  a .pos * a .zero * a .neg

/-- The ordered multiplication formula for sign recombination. -/
@[simp]
theorem signProduct_apply (a : ∀ s, (signSubalgebra ℒ θ s).bchSubgroup) :
    signProduct ℒ θ a = (a .pos : BCHGroup L) * a .zero * a .neg := (rfl)

end Product

variable [DecidableEq N] [GradedLieAlgebra ℒ]

section Nilpotent

variable [LieRing.IsNilpotent L]

private def signCoordinates : L ≃ (∀ s, (signSubalgebra ℒ θ s).bchSubgroup) where
  toFun x s := ⟨exp (signDecomposition ℒ θ x s : L), by simp⟩
  invFun a := ∑ s, log (a s : BCHGroup L)
  left_inv x := by simpa only [log_exp] using sum_signDecomposition ℒ θ x
  right_inv a := by
    let b : ∀ s, signSubalgebra ℒ θ s := fun s =>
      ⟨log (a s : BCHGroup L), (LieSubalgebra.mem_bchSubgroup _ _).mp (a s).property⟩
    have hb := (signDecomposition_eq_iff ℒ θ (∑ s, (b s : L)) b).mpr rfl
    funext s
    apply Subtype.ext
    apply log_injective
    simpa only [log_exp, b] using congrArg Subtype.val (hb s)

private def logSignProduct (x : L) : L :=
  log (signProduct ℒ θ (signCoordinates ℒ θ x))

private theorem logSignProduct_eq (x : L) :
    logSignProduct ℒ θ x =
      log (exp (signDecomposition ℒ θ x .pos : L) *
        exp (signDecomposition ℒ θ x .zero : L) *
        exp (signDecomposition ℒ θ x .neg : L)) := (rfl)

private theorem logSignProduct_add (K : LieIdeal R L)
    (hK : DirectSum.SetLike.IsHomogeneous ℒ K)
    (hc : K ≤ LieAlgebra.center R L) (x z : L) (hz : z ∈ K) :
    logSignProduct ℒ θ (x + z) = logSignProduct ℒ θ x + z := by
  let c (s : SignType) (y : L) : L := signDecomposition ℒ θ y s
  have hzK (s) : c s z ∈ K := signDecomposition_mem ℒ θ K.toSubmodule hK hz s
  have hcentral (s) (y : L) : ⁅y, c s z⁆ = 0 :=
    (LieModule.mem_maxTrivSubmodule R L L _).mp (hc (hzK s)) y
  have hcomm (s t) : Commute (exp (c s z)) (exp (c t x)) :=
    (commute_exp_of_lie_eq_zero _ _ (hcentral s (c t x))).symm
  have hsum : c .pos z + c .zero z + c .neg z = z := by
    simpa [c, SignType.univ_eq, add_comm, add_left_comm, add_assoc] using
      sum_signDecomposition ℒ θ z
  have he : exp z = exp (c .pos z) * exp (c .zero z) * exp (c .neg z) := by
    calc
      exp z = exp (c .pos z + c .zero z + c .neg z) := congrArg exp hsum.symm
      _ = _ := by
        rw [exp_add_of_lie_eq_zero _ _ (hcentral .neg _),
          exp_add_of_lie_eq_zero _ _ (hcentral .zero _)]
  have htranslate (s) : exp (c s (x + z)) = exp (c s x) * exp (c s z) := by
    have hcadd : c s (x + z) = c s x + c s z := by simp [c]
    rw [hcadd, exp_add_of_lie_eq_zero _ _ (hcentral s _)]
  have hformula (y : L) : exp (logSignProduct ℒ θ y) =
      exp (c .pos y) * exp (c .zero y) * exp (c .neg y) := by
    rw [logSignProduct_eq, exp_log]
  have heq : exp (logSignProduct ℒ θ (x + z)) = exp (logSignProduct ℒ θ x) * exp z := by
    rw [hformula, hformula, htranslate, htranslate, htranslate, he,
      (hcomm .pos .zero).mul_mul_mul_comm,
      ((hcomm .pos .neg).mul_left (hcomm .zero .neg)).mul_mul_mul_comm]
  have hzcentral : ⁅logSignProduct ℒ θ x, z⁆ = 0 :=
    (LieModule.mem_maxTrivSubmodule R L L _).mp (hc hz) _
  rw [← exp_add_of_lie_eq_zero _ _ hzcentral] at heq
  exact exp.injective heq

variable {L' : Type*} [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L']
  [IsScalarTower ℚ R L'] [LieRing.IsNilpotent L']
  (ℳ : N → Submodule R L') [GradedLieAlgebra ℳ]

private theorem map_logSignProduct (f : L →ₗ⁅R⁆ L')
    (hf : ∀ n, ∀ x ∈ ℒ n, f x ∈ ℳ n) (x : L) :
    f (logSignProduct ℒ θ x) = logSignProduct ℳ θ (f x) := by
  have hmap (s : SignType) : f (signDecomposition ℒ θ x s : L) =
      (signDecomposition ℳ θ (f x) s : L') :=
    map_signDecomposition ℒ θ ℳ f.toLinearMap.toAddMonoidHom hf x s
  rw [logSignProduct_eq, logSignProduct_eq]
  calc
    _ = log (f.bchGroupMap (exp (signDecomposition ℒ θ x .pos : L) *
        exp (signDecomposition ℒ θ x .zero : L) *
        exp (signDecomposition ℒ θ x .neg : L))) := (f.log_bchGroupMap _).symm
    _ = _ := by
      simp only [map_mul, LieHom.bchGroupMap_exp, hmap]

end Nilpotent

namespace PositiveDegrees

variable (d : PositiveDegrees N) [IsPositiveGrading d ℒ]

/-- Lowering the cutoff maps each sign subgroup onto the lower one. -/
theorem bchSubgroup_map_signSubalgebra_truncationMap {k l : ℕ} (h : k ≤ l) (s : SignType) :
    (signSubalgebra (d.truncatedGrading ℒ l) θ s).bchSubgroup.map
        (d.truncationMap ℒ h).bchGroupMap =
      (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup := by
  rw [← LieSubalgebra.bchSubgroup_map, d.map_signSubalgebra_truncationMap ℒ θ h s]

/-- Lower each sign factor along a decrease of the degree cutoff. -/
def lowerSignFactors {k l : ℕ} (h : k ≤ l)
    (a : ∀ s, (signSubalgebra (d.truncatedGrading ℒ l) θ s).bchSubgroup) :
    ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup :=
  fun s => ⟨(d.truncationMap ℒ h).bchGroupMap (a s), by
    rw [← bchSubgroup_map_signSubalgebra_truncationMap ℒ θ d h s]
    exact Subgroup.mem_map_of_mem _ (a s).property⟩

/-- Each lowered sign factor is the image of the original factor. -/
@[simp]
theorem coe_lowerSignFactors {k l : ℕ} (h : k ≤ l)
    (a : ∀ s, (signSubalgebra (d.truncatedGrading ℒ l) θ s).bchSubgroup) (s : SignType) :
    (lowerSignFactors ℒ θ d h a s : BCHGroup (d.truncatedLie ℒ k)) =
      (d.truncationMap ℒ h).bchGroupMap (a s) := (rfl)

/-- Lowering sign factors commutes with multiplying them. -/
theorem signProduct_lowerSignFactors {k l : ℕ} (h : k ≤ l)
    (a : ∀ s, (signSubalgebra (d.truncatedGrading ℒ l) θ s).bchSubgroup) :
    signProduct _ θ (lowerSignFactors ℒ θ d h a) =
      (d.truncationMap ℒ h).bchGroupMap (signProduct _ θ a) := by
  simp

/-- Every family of lower sign factors lifts along a decrease of the cutoff. -/
theorem lowerSignFactors_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (lowerSignFactors ℒ θ d h) := by
  have hs := Function.Surjective.piMap fun s => (MulEquiv.subgroupCongr
    (bchSubgroup_map_signSubalgebra_truncationMap ℒ θ d h s)).surjective.comp
      ((d.truncationMap ℒ h).bchGroupMap.subgroupMap_surjective
        (signSubalgebra (d.truncatedGrading ℒ l) θ s).bchSubgroup)
  convert hs using 1
  ext a s
  rfl

private theorem logSignProduct_truncated_bijective (k : ℕ) :
    Function.Bijective (logSignProduct (d.truncatedGrading ℒ k) θ) := by
  induction k with
  | zero =>
    exact ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  | succ k ih =>
    let p := d.truncationMap ℒ (Nat.le_succ k)
    apply p.toLinearMap.toAddMonoidHom.bijective_of_semiconj_of_add_ker
      (d.truncationMap_surjective ℒ (Nat.le_succ k)) _ _ ih
    · intro x
      exact map_logSignProduct (d.truncatedGrading ℒ (k + 1)) θ
        (d.truncatedGrading ℒ k) p
        (fun n x hx => by
          rw [← d.map_truncatedGrading_truncationMap ℒ (Nat.le_succ k) n]
          exact Submodule.mem_map_of_mem hx) x
    · intro x z hz
      exact logSignProduct_add (d.truncatedGrading ℒ (k + 1)) θ p.ker
        (d.ker_truncationMap_isHomogeneous ℒ (Nat.le_succ k))
        (d.ker_truncationMap_succ_le_center ℒ k) x z hz

/-- Multiplication of positive, zero and negative sign subgroups is bijective at
every finite cutoff, over any commutative rational coefficient algebra. -/
theorem signProduct_bijective (k : ℕ) :
    Function.Bijective (signProduct (d.truncatedGrading ℒ k) θ) := by
  have h := (logSignProduct_truncated_bijective ℒ θ d k).comp
    (signCoordinates (d.truncatedGrading ℒ k) θ).symm.bijective
  have h' := exp.bijective.comp h
  simpa only [Function.comp_def, logSignProduct, Equiv.apply_symm_apply, exp_log] using h'

/-- Ordered sign factorization at a finite cutoff. Its inverse extracts the
unique positive, zero and negative factors of a BCH element. -/
def signFactorizationEquiv (k : ℕ) :
    (∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup) ≃
      d.truncatedGroup ℒ k :=
  Equiv.ofBijective _ (signProduct_bijective ℒ θ d k)

/-- The forward equivalence multiplies in positive-zero-negative order. -/
@[simp]
theorem signFactorizationEquiv_apply (k : ℕ)
    (a : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup) :
    signFactorizationEquiv ℒ θ d k a = (a .pos : d.truncatedGroup ℒ k) * a .zero * a .neg :=
  (rfl)

/-- All three sign factors of the identity are identities. -/
@[simp]
theorem signFactorizationEquiv_symm_one (k : ℕ) :
    (signFactorizationEquiv ℒ θ d k).symm 1 = 1 := by
  apply (signFactorizationEquiv ℒ θ d k).symm_apply_eq.mpr
  simp only [signFactorizationEquiv_apply, Pi.one_apply, OneMemClass.coe_one, one_mul]

/-- Each sign factor is compatible with lowering the degree cutoff. -/
@[simp]
theorem truncationMap_signFactorizationEquiv_symm {k l : ℕ} (h : k ≤ l)
    (g : d.truncatedGroup ℒ l) (s : SignType) :
    (d.truncationMap ℒ h).bchGroupMap
        ((signFactorizationEquiv ℒ θ d l).symm g s : d.truncatedGroup ℒ l) =
      ((signFactorizationEquiv ℒ θ d k).symm
        ((d.truncationMap ℒ h).bchGroupMap g) s : d.truncatedGroup ℒ k) := by
  let a := (signFactorizationEquiv ℒ θ d l).symm g
  have hb : signFactorizationEquiv ℒ θ d k (lowerSignFactors ℒ θ d h a) =
      (d.truncationMap ℒ h).bchGroupMap g := by
    rw [signFactorizationEquiv_apply, ← signProduct_apply, signProduct_lowerSignFactors]
    simpa only [signFactorizationEquiv_apply, signProduct_apply] using
      congrArg (d.truncationMap ℒ h).bchGroupMap
        ((signFactorizationEquiv ℒ θ d l).apply_symm_apply g)
  exact congrArg (fun a => (a s : d.truncatedGroup ℒ k))
    ((signFactorizationEquiv ℒ θ d k).eq_symm_apply.mpr hb)

end PositiveDegrees
end Mei
