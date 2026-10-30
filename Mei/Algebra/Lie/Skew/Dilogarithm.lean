/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Skew.Ray
public import Mei.RingTheory.PowerSeries.Dilogarithm

/-!
# Dilogarithm elements of the completed skew group

For a nonzero allowed degree `n` of positive degree data on the exponent group of a skew
Lie algebra over a commutative `ℚ`-algebra, the dilogarithm element is
`Ψ[n] = exp(∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` in the completed BCH group. It is the
ray label of the power series `-Li₂(-X)` (`PowerSeries.negDilogNeg`): at order `k` it is
the exponential of the class of the finite sum over `j ≤ k`, and these levelwise
exponentials are compatible under truncation. Its logarithmic coefficients are
`(-1)^(j+1)/j² X_{jn}` on the positive multiples of `n` and zero elsewhere.

`Ψ[n]` lies in the completed subgroup of the supported ray through `n`, so dilogarithm
elements of degrees on one ray commute. Rational powers, such as the normalized factors
`Ψ[tn]^(s κ(tn))`, are given by the ray labels `rayExp (c • negDilogNeg R)`; for integers
`c` these are the group powers, by `rayExp_zsmul`.

For a finite product of dilogarithm powers at distinct degrees, removing the factors of
smaller degree leaves a filtered label whose coefficient in the first retained degree is
the exponent times its skew generator. This identifies the leading coefficient in
inductive arguments about such products.

The elements and their conventions follow Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 (arXiv:1411.1394v2), and Nakanishi, *Cluster algebras and scattering
diagrams, Part III*, §5.1 (arXiv:2111.00800v6).
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries

variable {R Γ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

local notation "𝔤" => positiveLieAlgebra β hβ d
local notation "ℒ" => positiveGrading β hβ d

/-- The dilogarithm element `Ψ[n] = exp(∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` of a nonzero
allowed degree `n`, in the completed BCH group of the positive skew Lie algebra. -/
def dilogElement : d.completedBCHGroup ℒ :=
  rayExp β hβ hn hn0 (negDilogNeg R)

theorem dilogElement_def : dilogElement β hβ hn hn0 = rayExp β hβ hn hn0 (negDilogNeg R) :=
  (rfl)

/-- At order `k`, `Ψ[n]` is the exponential of the class of
`∑_{j < k} (-1)^j / (j+1)² X_{(j+1)n}`. -/
theorem projection_dilogElement (k : ℕ) :
    CompletedGroup.projection k (dilogElement β hβ hn hn0) =
      BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ (∑ j ∈ Finset.range k,
        rayGenerator β hβ hn hn0 j (algebraMap ℚ R ((-1) ^ j / ((j : ℚ) + 1) ^ 2)))) := by
  simp only [dilogElement, projection_rayExp, rayPartialSum_apply, coeff_succ_negDilogNeg]
  -- Both sides are the same exponential, typed in the tower object and the truncated group.
  rfl

/-- The logarithmic coefficient of `Ψ[n]` in degree `(j+1)n` is
`(-1)^j / (j+1)² X_{(j+1)n}`. -/
@[simp]
theorem logComponent_dilogElement_succ_nsmul (j : ℕ) :
    (d.logComponent ℒ (dilogElement β hβ hn hn0) ((j + 1) • n) : 𝔤) =
      rayGenerator β hβ hn hn0 j (algebraMap ℚ R ((-1) ^ j / ((j : ℚ) + 1) ^ 2)) := by
  rw [dilogElement, logComponent_rayExp_succ_nsmul, coeff_succ_negDilogNeg]

/-- Off the positive multiples of `n`, `Ψ[n]` has no logarithmic coefficient. -/
theorem logComponent_dilogElement_eq_zero_of_forall_ne {m : Γ} (hm : ∀ j : ℕ, (j + 1) • n ≠ m) :
    d.logComponent ℒ (dilogElement β hβ hn hn0) m = 0 :=
  logComponent_rayExp_eq_zero_of_forall_ne β hβ hn hn0 _ hm

/-- `Ψ[n]` lies in the completed subgroup of the supported ray through `n`. -/
theorem dilogElement_mem_completedRaySubgroup {w : SupportedRay d} (hw : n ∈ w.rayDegrees) :
    dilogElement β hβ hn hn0 ∈ d.completedRaySubgroup ℒ w :=
  rayExp_mem_completedRaySubgroup β hβ hn hn0 hw _

/-- Dilogarithm elements of degrees on one supported ray commute. -/
theorem commute_dilogElement {n' : Γ} (hn' : n' ∈ d.monoid) (hn0' : n' ≠ 0)
    {w : SupportedRay d} (hw : n ∈ w.rayDegrees) (hw' : n' ∈ w.rayDegrees) :
    Commute (dilogElement β hβ hn hn0) (dilogElement β hβ hn' hn0') :=
  d.commute_of_mem_completedRaySubgroup ℒ (dilogElement_mem_completedRaySubgroup β hβ hn hn0 hw)
    (dilogElement_mem_completedRaySubgroup β hβ hn' hn0' hw')

/-- Removing from a finite product `C` of dilogarithm powers at distinct degrees the factors
of degree smaller than that of `mᵢ`, from a label `g` that agrees with `C` at an order at least
`deg mᵢ = a + 1`, leaves a label in the degree filtration above order `a` whose coefficient in
degree `mᵢ` is `cᵢ X_{mᵢ}`. -/
theorem inv_prod_filter_mul_mem_and_logComponent {r : ℕ} (m : Fin r → Γ)
    (hm : ∀ j, m j ∈ d.monoid) (hm0 : ∀ j, m j ≠ 0) (hinj : Function.Injective m)
    (c : Fin r → R) {g : d.completedBCHGroup ℒ} {k : ℕ}
    (hk : CompletedGroup.projection k g = CompletedGroup.projection k
      ((List.finRange r).map fun j =>
        SkewLieAlgebra.rayExp β hβ (hm j) (hm0 j) (c j • negDilogNeg R)).prod)
    (i : Fin r) {a : ℕ} (hia : d.degree (m i) = (a + 1 : ℕ)) (hik : a + 1 ≤ k) :
    (((List.finRange r).filter fun j => d.degree (m j) < d.degree (m i)).map fun j =>
        SkewLieAlgebra.rayExp β hβ (hm j) (hm0 j) (c j • negDilogNeg R)).prod⁻¹ * g ∈
      CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) ∧
    ((d.logComponent ℒ ((((List.finRange r).filter fun j => d.degree (m j) < d.degree (m i)).map
        fun j => SkewLieAlgebra.rayExp β hβ (hm j) (hm0 j) (c j • negDilogNeg R)).prod⁻¹ * g)
          (m i) : 𝔤) : SkewLieAlgebra β hβ) = SkewLieAlgebra.single β hβ (m i) (c i) := by
  classical
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Fin r → d.completedBCHGroup ℒ, Ψ = fun j =>
    SkewLieAlgebra.rayExp β hβ (hm j) (hm0 j) (c j • negDilogNeg R) := ⟨_, rfl⟩
  rw [← hΨ] at hk ⊢
  let p : Fin r → Prop := fun j => d.degree (m j) < d.degree (m i)
  obtain ⟨w, hw⟩ : ∃ w, w = (((List.finRange r).filter p).map Ψ).prod := ⟨_, rfl⟩
  rw [← hw]
  -- `g C⁻¹` vanishes at order `k`; the factors of degree at least `deg mᵢ` lie in the
  -- filtration above order `a`, and their coefficients in degrees at most `a + 1` add up.
  have hgC : g * ((List.finRange r).map Ψ).prod⁻¹ ∈
      CompletedGroup.degreeFiltration (d.groupTower ℒ) (k + 1) := by
    rw [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker, map_mul, map_inv, hk,
      mul_inv_cancel]
  have hx : ∀ j ∈ List.finRange r, ¬p j →
      Ψ j ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) := fun j _ hj => by
    rw [hΨ]
    exact SkewLieAlgebra.rayExp_mem_degreeFiltration β hβ (hm j) (hm0 j) _
      (by simp only [p, not_lt] at hj; omega)
  obtain ⟨hwC, hcomp⟩ :=
    d.inv_prod_filter_mul_prod_mem_degreeFiltration_and_logComponent (List.finRange r) Ψ p hx
  rw [← hw] at hwC hcomp
  -- Write `w⁻¹ g` as a conjugate of `g C⁻¹` times `w⁻¹ C`.
  have hconj : w⁻¹ * (g * ((List.finRange r).map Ψ).prod⁻¹) * w⁻¹⁻¹ ∈
      CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1 + 1) :=
    (CompletedGroup.degreeFiltration_normal _ _).conj_mem _
      (CompletedGroup.degreeFiltration_antitone _ (by omega) hgC) _
  have hdecomp : w⁻¹ * g = (w⁻¹ * (g * ((List.finRange r).map Ψ).prod⁻¹) * w⁻¹⁻¹) *
      (w⁻¹ * ((List.finRange r).map Ψ).prod) := by group
  refine ⟨hdecomp ▸ Subgroup.mul_mem _
    (CompletedGroup.degreeFiltration_antitone _ (by omega) hconj) hwC, ?_⟩
  -- Among the remaining factors only `Ψ[mᵢ]^{cᵢ}` has a coefficient in degree `mᵢ`.
  have hlog : d.logComponent ℒ (w⁻¹ * g) (m i) = d.logComponent ℒ (Ψ i) (m i) := by
    rw [hdecomp, d.logComponent_mul_of_mem_degreeFiltration (a := a) (b := a)
        (CompletedGroup.degreeFiltration_antitone _ (by omega) hconj) hwC (by omega),
      d.mem_degreeFiltration_succ_iff.mp hconj (m i) (by omega), zero_add,
      hcomp (m i) (by omega), ← List.sum_toFinset _ ((List.nodup_finRange r).filter _)]
    refine Finset.sum_eq_single_of_mem i (by simp [p]) fun j hj hji => ?_
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, p, not_lt] at hj
    rw [hΨ]
    refine SkewLieAlgebra.logComponent_rayExp_eq_zero_of_forall_ne β hβ (hm j) (hm0 j) _
      fun t ht => ?_
    rcases t with _ | t
    · exact hji (hinj (by simpa using ht))
    · have h₁ := congrArg d.degree ht
      rw [map_nsmul, nsmul_eq_mul] at h₁
      push_cast at h₁
      have := d.degree_pos (hm j) (hm0 j)
      nlinarith
  -- That coefficient is `cᵢ X_{mᵢ}`, the linear term of `cᵢ ∑_j (-1)^(j+1) X_{j mᵢ} / j²`.
  have key : ∀ q, q = (0 + 1) • m i →
      ((d.logComponent ℒ (Ψ i) q : 𝔤) : SkewLieAlgebra β hβ) =
        SkewLieAlgebra.single β hβ q (c i) := by
    rintro q rfl
    rw [hΨ]
    simp only [SkewLieAlgebra.logComponent_rayExp_succ_nsmul, SkewLieAlgebra.coe_rayGenerator,
      PowerSeries.coeff_smul, coeff_negDilogNeg]
    norm_num
  rw [hlog]
  exact key _ (by rw [zero_add, one_nsmul])

end Mei.SkewLieAlgebra
