/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Stratification

/-!
# A branch stratification of the folding map

The absolute value `x ↦ |x|` on `ℝ`, with the integral lattice `ℤ`, is a single-chart finite
semilinear family (`foldFamily`). Its pieces are the three sign sets `{x < 0}`, `{0}` and
`{x > 0}`, on which it is `-x`, `0` and `x`. They form a branch stratification
(`foldStratification`) over the three target strata `{w < 0}`, `{0}` and `{w > 0}`: the
negative and positive half-lines both lie over `{w > 0}`, the point `0` lies over `{0}`, and
nothing lies over `{w < 0}`. Hence the fiber over `w` has two points for `w > 0`, one for
`w = 0` and none for `w < 0` (`nat_card_fiber_foldFamily_of_pos`,
`nat_card_fiber_foldFamily_zero`, `nat_card_fiber_foldFamily_of_neg`).
-/

public section

open Set

namespace Mei.FiniteSemilinearFamily.Examples

variable (h : TauCeti.Toric.IsIntegralLattice (Int.castAddHom ℝ))

/-- The multiplication by a sign `σ` as an affine map of `ℝ`. -/
def signSMul (σ : SignType) : ℝ →ᵃ[ℝ] ℝ := ((σ : ℝ) • LinearMap.id).toAffineMap

@[simp]
theorem signSMul_apply (σ : SignType) (x : ℝ) : signSMul σ x = σ * x := by
  simp [signSMul]

@[simp]
theorem signSMul_linear (σ : SignType) : (signSMul σ).linear = (σ : ℝ) • LinearMap.id := by
  simp [signSMul]

/-- Multiplication by a sign has rational linear part. -/
theorem isRationalLinearMap_signSMul (σ : SignType) :
    Toric.IsRationalLinearMap h h (signSMul σ).linear := by
  have hσ : (σ : ℝ) = ((σ : ℚ) : ℝ) := by cases σ <;> simp
  rw [signSMul_linear, hσ]
  exact (Toric.IsRationalLinearMap.id h).rat_smul _

/-- The level set of the sign function at `σ` is a locally closed polyhedron. -/
theorem isLocallyClosedPolyhedron_setOf_sign_eq (σ : SignType) :
    IsLocallyClosedPolyhedron h {x : ℝ | SignType.sign x = σ} := by
  -- The level set is the sign cell of the single row `x ↦ x`.
  let r : ℝ →ᴬ[ℝ] ℝ := (ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
  have hr : Toric.IsRationalFunctional h r.toAffineMap.linear := by
    have hlin : r.toAffineMap.linear = h.realCharacter (LinearMap.id : Module.Dual ℤ ℤ) :=
      h.eq_realCharacter fun n => by
        rw [ContinuousAffineMap.coe_linear_eq_coe_contLinear]
        simp [r]
    exact hlin ▸ Toric.IsRationalFunctional.realCharacter h LinearMap.id
  have hcell : {x : ℝ | SignType.sign x = σ} = Convex.signCell (fun _ : Unit => r) fun _ => σ := by
    ext x
    simp [r]
  exact hcell ▸ isLocallyClosedPolyhedron_signCell _ (fun _ => hr) _

/-- On the level set of the sign function at `σ`, the absolute value is multiplication by `σ`. -/
theorem abs_eq_signSMul {σ : SignType} {x : ℝ} (hx : SignType.sign x = σ) :
    |x| = signSMul σ x := by
  subst hx
  rw [signSMul_apply, sign_mul_self]

/-- The absolute value on `ℝ` is piecewise affine with rational linear parts. -/
theorem isRationalPiecewiseAffine_abs :
    IsRationalPiecewiseAffine h h (univ : Set ℝ) fun x => |x.1| :=
  (isRationalPiecewiseAffine_iff).mpr ⟨SignType, inferInstance,
    fun σ => {x : ℝ | SignType.sign x = σ}, signSMul,
    eq_univ_of_forall fun _ => mem_iUnion.mpr ⟨_, rfl⟩, fun σ =>
      ⟨(isLocallyClosedPolyhedron_setOf_sign_eq h σ).isRationalSemilinear,
        isRationalLinearMap_signSMul h σ, fun _ hx => abs_eq_signSMul hx⟩⟩

/-- The folding family: a single chart, the absolute value on `ℝ`. -/
noncomputable def foldFamily : FiniteSemilinearFamily h h Unit :=
  single (isRationalPiecewiseAffine_abs h)

@[simp]
theorem foldFamily_domain (c : Unit) : (foldFamily h).domain c = univ := by
  simp [foldFamily]

@[simp]
theorem foldFamily_eval (c : Unit) (x : (foldFamily h).domain c) :
    (foldFamily h).eval c x = |x.1| := by
  simp [foldFamily]

/-- Multiplication by `σ` maps the level set of the sign function at `σ` bijectively onto the
level set at `σ * σ`. -/
theorem bijOn_signSMul (σ : SignType) : BijOn (signSMul σ) {x : ℝ | SignType.sign x = σ}
    {w : ℝ | SignType.sign w = σ * σ} := by
  cases σ
  · exact ⟨fun _ _ => by simp, fun _ hx _ hy _ => by simp_all,
      fun _ hw => ⟨0, by simp_all⟩⟩
  · refine ⟨fun x hx => ?_, fun x _ y _ hxy => by simpa using hxy, fun w hw => ⟨-w, ?_⟩⟩
    · simp_all [sign_eq_neg_one_iff, sign_eq_one_iff]
    · simp_all [sign_eq_neg_one_iff, sign_eq_one_iff]
  · exact ⟨fun _ hx => by simpa using hx, fun _ _ _ _ hxy => by simpa using hxy,
      fun w hw => ⟨w, by simpa using hw, by simp⟩⟩

/-- The branch stratification of the folding family by signs: the source stratum `σ` is the
level set of the sign at `σ`, on which the folding map is multiplication by `σ`, mapping it onto
the target stratum `σ * σ`. -/
noncomputable def foldStratification : (foldFamily h).BranchStratification SignType SignType where
  target σ := {w : ℝ | SignType.sign w = σ}
  chart _ := ()
  source σ := {x : ℝ | SignType.sign x = σ}
  stratum σ := σ * σ
  nonempty_target σ := by
    cases σ
    exacts [⟨0, by simp⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩]
  isLocallyClosedPolyhedron_target := isLocallyClosedPolyhedron_setOf_sign_eq h
  pairwise_disjoint_target σ τ hστ := disjoint_left.mpr fun x hx hy => hστ (hx.symm.trans hy)
  iUnion_target := eq_univ_of_forall fun x => mem_iUnion.mpr ⟨_, rfl⟩
  isLocallyClosedPolyhedron_source := isLocallyClosedPolyhedron_setOf_sign_eq h
  domain_eq _ := by
    simp only [foldFamily_domain, iUnion_true]
    exact (eq_univ_of_forall fun x => mem_iUnion.mpr ⟨_, rfl⟩).symm
  disjoint_source σ τ _ hστ := disjoint_left.mpr fun x hx hy => hστ (hx.symm.trans hy)
  exists_affineMap σ := ⟨signSMul σ, isRationalLinearMap_signSMul h σ, bijOn_signSMul σ,
    fun x hx => by simpa using abs_eq_signSMul hx⟩

@[simp]
theorem foldStratification_target (σ : SignType) :
    (foldStratification h).target σ = {w : ℝ | SignType.sign w = σ} := by
  simp [foldStratification]

@[simp]
theorem foldStratification_chart (σ : SignType) : (foldStratification h).chart σ = () := by
  simp [foldStratification]

@[simp]
theorem foldStratification_source (σ : SignType) :
    (foldStratification h).source σ = {x : ℝ | SignType.sign x = σ} := by
  simp [foldStratification]

@[simp]
theorem foldStratification_stratum (σ : SignType) : (foldStratification h).stratum σ = σ * σ := by
  simp [foldStratification]

/-- Over a positive point the folding family has two points: one in each half-line. -/
theorem nat_card_fiber_foldFamily_of_pos {w : ℝ} (hw : 0 < w) :
    Nat.card ((foldFamily h).fiber w) = 2 := by
  rw [(foldStratification h).nat_card_fiber (b := 1) (by simpa [sign_eq_one_iff] using hw),
    Nat.card_eq_fintype_card]
  simp only [foldStratification_stratum]
  decide

/-- Over zero the folding family has one point. -/
theorem nat_card_fiber_foldFamily_zero : Nat.card ((foldFamily h).fiber 0) = 1 := by
  rw [(foldStratification h).nat_card_fiber (b := 0) (by simp),
    Nat.card_eq_fintype_card]
  simp only [foldStratification_stratum]
  decide

/-- Over a negative point the folding family is empty. -/
theorem nat_card_fiber_foldFamily_of_neg {w : ℝ} (hw : w < 0) :
    Nat.card ((foldFamily h).fiber w) = 0 := by
  rw [(foldStratification h).nat_card_fiber (b := -1) (by simpa [sign_eq_neg_one_iff] using hw),
    Nat.card_eq_fintype_card]
  simp only [foldStratification_stratum]
  decide

end Mei.FiniteSemilinearFamily.Examples
