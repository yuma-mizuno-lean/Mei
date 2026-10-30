/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mei.Analysis.Convex.Sign
public import Mei.Geometry.Toric.Algebraic.DualLattice
public import Mei.LinearAlgebra.Dual.Order
public import Mathlib.Topology.Instances.Sign

/-!
# Real dual models for scattering diagrams

A `KSSpace` identifies a real vector space carrying the integral dual lattice
with the real characters of the degree group. Its evaluation normals are the
real extensions of integral evaluation. The degree functional gives a point
strictly on the positive side of every allowed-degree hyperplane. Small
displacements in its direction preserve nonzero retained evaluation signs
and move all vanishing retained evaluations to the sign of the displacement.
In a projective degree group a degree is determined by its normal, so two nonzero
allowed degrees with nested normal kernels have equal positive multiples.

`KSSpace.ofLattice` constructs the model for any finite free degree lattice.
It uses `Module.evalEquiv` for integral double duality and
`IsIntegralLattice.exists_realCharacter_apply_eq` for real extension. The normal
comparison uses `IsIntegralLattice.eq_realCharacter`.
-/

public section

noncomputable section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : (N →+ ℤ) →+ V}

/-- A model of the real character space with its compatible integral dual lattice. -/
structure KSSpace (h : TauCeti.Toric.IsIntegralLattice i) where
  /-- Evaluation identifies spatial points with real characters of the degree group. -/
  evaluation : V ≃ₗ[ℝ] (N →+ ℝ)
  /-- Integral lattice points evaluate as the corresponding integral characters. -/
  evaluation_lattice : ∀ m n, evaluation (i m) n = (m n : ℝ)

attribute [simp] KSSpace.evaluation_lattice

namespace KSSpace

variable {h : TauCeti.Toric.IsIntegralLattice i} (s : KSSpace h)

/-- The evaluation equivalence determines a real dual model. -/
@[ext]
theorem ext {s t : KSSpace h} (he : s.evaluation = t.evaluation) : s = t := by
  cases s
  cases t
  cases he
  rfl

/-- An integral dual lattice supplies its real character-space model when the
degree group is a finite free integer module. -/
def ofLattice [Module.Free ℤ N] [Module.Finite ℤ N]
    (h : TauCeti.Toric.IsIntegralLattice i) : KSSpace h := by
  let := h.finiteDimensional
  let e : N ≃+ ((N →+ ℤ) →+ ℤ) := AddEquiv.ofBijective AddMonoidHom.eval (by
    constructor
    · intro x y he
      apply (Module.evalEquiv ℤ N).injective
      ext f
      exact DFunLike.congr_fun he f.toAddMonoidHom
    · intro f
      let f' : Module.Dual ℤ (Module.Dual ℤ N) :=
        f.toIntLinearMap.comp (addMonoidHomLequivInt ℤ).symm.toLinearMap
      refine ⟨(Module.evalEquiv ℤ N).symm f', ?_⟩
      ext m
      exact (Module.apply_evalEquiv_symm_apply ℤ N m.toIntLinearMap f').trans (by rfl))
  let ev : V →ₗ[ℝ] (N →+ ℝ) :=
    { toFun := fun θ =>
        { toFun := fun n => h.realCharacter (AddMonoidHom.eval n) θ
          map_zero' := by simp
          map_add' := by intros; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine
    { evaluation := LinearEquiv.ofBijective ev ⟨?_, ?_⟩
      evaluation_lattice := by intros; exact h.realCharacter_apply _ _ }
  · intro x y he
    apply (Module.evalEquiv ℝ V).injective
    apply h.dual.isBaseChange.algHom_ext
    intro m
    obtain ⟨n, rfl⟩ := e.surjective m
    exact DFunLike.congr_fun he n
  · intro f
    obtain ⟨θ, hθ⟩ := h.exists_realCharacter_apply_eq (f.comp e.symm.toAddMonoidHom)
    refine ⟨θ, ?_⟩
    ext n
    exact (hθ (e n)).trans (congrArg f (e.symm_apply_apply n))

/-- The constructed evaluation is real extension of integral evaluation. -/
@[simp]
theorem ofLattice_evaluation [Module.Free ℤ N] [Module.Finite ℤ N]
    (h : TauCeti.Toric.IsIntegralLattice i) (θ : V) (n : N) :
    (ofLattice h).evaluation θ n = h.realCharacter (AddMonoidHom.eval n) θ := (rfl)

/-- The continuous dual of a lattice is its canonical real character-space model.
The required finite freeness follows from the original integral lattice. -/
def continuousDual {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {j : N →+ W} (h : TauCeti.Toric.IsIntegralLattice j) : KSSpace h.continuousDual := by
  letI := h.free
  letI := h.finite
  exact ofLattice h.continuousDual

/-- In the continuous-dual model, evaluation is ordinary evaluation on lattice vectors. -/
@[simp]
theorem continuousDual_evaluation {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {j : N →+ W} (h : TauCeti.Toric.IsIntegralLattice j) (θ : W →L[ℝ] ℝ) (n : N) :
    (continuousDual h).evaluation θ n = θ (j n) := by
  simp [continuousDual, ofLattice_evaluation]

/-- The linear normal associated to a degree. -/
def normal (n : N) : V →ₗ[ℝ] ℝ where
  toFun θ := s.evaluation θ n
  map_add' θ η := by simp
  map_smul' r θ := by simp

/-- The degree normal evaluates the spatial character at that degree. -/
@[simp]
theorem normal_apply (n : N) (θ : V) : s.normal n θ = s.evaluation θ n := (rfl)

/-- Degree normals are the real extensions of integral evaluation on the dual lattice. -/
theorem normal_eq_realCharacter (n : N) :
    s.normal n = h.realCharacter (AddMonoidHom.eval n) :=
  h.eq_realCharacter (fun m => s.evaluation_lattice m n)

/-- The point representing the positive degree functional. -/
def degreePoint (d : PositiveDegrees N) : V :=
  s.evaluation.symm ((Int.castAddHom ℝ).comp d.degree)

/-- The character of the degree point is the cutoff degree. -/
@[simp]
theorem evaluation_degreePoint (d : PositiveDegrees N) (n : N) :
    s.evaluation (s.degreePoint d) n = (d.degree n : ℝ) := by
  simp [degreePoint]

/-- The degree point is positive on every nonzero allowed degree. -/
theorem evaluation_degreePoint_pos (d : PositiveDegrees N) {n : N}
    (hn : n ∈ d.monoid) (hn0 : n ≠ 0) : 0 < s.evaluation (s.degreePoint d) n := by
  rw [evaluation_degreePoint]
  exact Int.cast_pos.mpr (d.degree_pos hn hn0)

/-- The negated degree point is negative on every nonzero allowed degree. -/
theorem evaluation_neg_degreePoint_neg (d : PositiveDegrees N) {n : N}
    (hn : n ∈ d.monoid) (hn0 : n ≠ 0) : s.evaluation (-s.degreePoint d) n < 0 := by
  rw [map_neg, AddMonoidHom.neg_apply]
  exact neg_neg_of_pos (s.evaluation_degreePoint_pos d hn hn0)

/-- Every nonzero allowed degree has a nonzero normal, without a saturation assumption. -/
theorem normal_ne_zero (d : PositiveDegrees N) {n : N}
    (hn : n ∈ d.monoid) (hn0 : n ≠ 0) : s.normal n ≠ 0 := by
  intro he
  have hz := LinearMap.congr_fun he (s.degreePoint d)
  have hp : (0 : ℝ) < d.degree n := Int.cast_pos.mpr (d.degree_pos hn hn0)
  rw [normal_apply, evaluation_degreePoint, LinearMap.zero_apply] at hz
  exact hp.ne' hz

/-- The zero degree has the zero normal. -/
@[simp]
theorem normal_zero : s.normal 0 = 0 := by
  ext θ
  simp

/-- In a projective degree group, for instance a free one, a degree with zero normal is zero:
real characters separate its points. -/
@[simp]
theorem normal_eq_zero_iff [Module.Projective ℤ N] {n : N} : s.normal n = 0 ↔ n = 0 := by
  refine ⟨fun hn => ?_, fun hn => hn ▸ s.normal_zero⟩
  by_contra hne
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℤ hne
  have he := LinearMap.congr_fun hn
    (s.evaluation.symm ((Int.castAddHom ℝ).comp f.toAddMonoidHom))
  simp only [normal_apply, LinearEquiv.apply_symm_apply, AddMonoidHom.coe_comp,
    Function.comp_apply, LinearMap.toAddMonoidHom_coe, Int.coe_castAddHom,
    LinearMap.zero_apply, Int.cast_eq_zero] at he
  exact hf he

/-- Two nonzero allowed degrees whose normals have nested kernels have equal positive
natural multiples. The multipliers are read off at the degree point, on which both normals
are positive. -/
theorem exists_nsmul_eq_nsmul_of_ker_normal_le [Module.Projective ℤ N] (d : PositiveDegrees N)
    {n m : N} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hm : m ∈ d.monoid) (hm0 : m ≠ 0)
    (hker : LinearMap.ker (s.normal n) ≤ LinearMap.ker (s.normal m)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • m = b • n := by
  obtain ⟨c, -, hc⟩ := LinearMap.exists_pos_smul_eq_of_ker_le_ker (s.normal n) (s.normal m)
    hker (s.evaluation_degreePoint_pos d hn hn0) (s.evaluation_degreePoint_pos d hm hm0)
  have hdn := d.degree_pos hn hn0
  have hdm := d.degree_pos hm hm0
  have hcd : c * d.degree n = d.degree m := by
    simpa using LinearMap.congr_fun hc (s.degreePoint d)
  refine ⟨(d.degree n).toNat, (d.degree m).toNat, by omega, by omega, ?_⟩
  rw [← sub_eq_zero, ← s.normal_eq_zero_iff]
  ext θ
  have hθ : c * s.evaluation θ n = s.evaluation θ m := by
    simpa using LinearMap.congr_fun hc θ
  have hn' : ((d.degree n).toNat : ℝ) = d.degree n := by exact_mod_cast Int.toNat_of_nonneg hdn.le
  have hm' : ((d.degree m).toNat : ℝ) = d.degree m := by exact_mod_cast Int.toNat_of_nonneg hdm.le
  simp only [normal_apply, map_sub, map_nsmul, nsmul_eq_mul, hn', hm', ← hθ, ← hcd,
    LinearMap.zero_apply]
  ring

/-- In rank one, vanishing on any nonzero degree forces the spatial point to be zero. -/
theorem evaluation_eq_zero_iff_of_int_ne_zero
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {j : (ℤ →+ ℤ) →+ W} {h : TauCeti.Toric.IsIntegralLattice j}
    (s : KSSpace h) {n : ℤ} (hn : n ≠ 0) (θ : W) :
    s.evaluation θ n = 0 ↔ θ = 0 := by
  constructor
  · intro hθ
    apply s.evaluation.injective
    rw [map_zero]
    apply AddMonoidHom.ext_int
    have hmul : (n : ℝ) * s.evaluation θ 1 = 0 := by
      rwa [AddMonoidHom.apply_int ℝ _ n, zsmul_eq_mul] at hθ
    exact (mul_eq_zero.mp hmul).resolve_left (Int.cast_ne_zero.mpr hn)
  · rintro rfl
    simp

section SignRegions

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i} (s : KSSpace h)

/-- The points where every degree of `S` evaluates with sign `σ` form a convex set. -/
theorem convex_setOf_forall_sign_evaluation_eq (S : Set N) (σ : SignType) :
    Convex ℝ {θ : V | ∀ n ∈ S, SignType.sign (s.evaluation θ n) = σ} := by
  have he : {θ : V | ∀ n ∈ S, SignType.sign (s.evaluation θ n) = σ} =
      ⋂ n ∈ S, s.normal n ⁻¹' {a : ℝ | SignType.sign a = σ} := by
    ext θ
    simp [normal_apply]
  rw [he]
  exact convex_iInter₂ fun n _ => (convex_setOf_sign_eq σ).linear_preimage (s.normal n)

/-- The points where every degree of a finite set `S` evaluates with the nonzero sign `σ`
form an open set. -/
theorem isOpen_setOf_forall_sign_evaluation_eq {S : Set N} (hS : S.Finite)
    {σ : SignType} (hσ : σ ≠ 0) :
    IsOpen {θ : V | ∀ n ∈ S, SignType.sign (s.evaluation θ n) = σ} := by
  let := h.finiteDimensional
  have he : {θ : V | ∀ n ∈ S, SignType.sign (s.evaluation θ n) = σ} =
      ⋂ n ∈ S, s.normal n ⁻¹' {a : ℝ | SignType.sign a = σ} := by
    ext θ
    simp [normal_apply]
  rw [he]
  exact hS.isOpen_biInter fun n _ =>
    (isOpen_setOf_sign_eq hσ).preimage (s.normal n).continuous_of_finiteDimensional

end SignRegions

/-- A sufficiently small displacement in the degree direction preserves every
nonzero retained evaluation sign, while a zero evaluation acquires the sign
of the displacement parameter. Both directions and the zero parameter are included. -/
theorem eventually_sign_evaluation_add_smul_degreePoint (d : PositiveDegrees N)
    (k : ℕ) (θ : V) :
    ∀ᶠ a : ℝ in nhds 0, ∀ n ∈ d.cutoff k \ {0},
      SignType.sign (s.evaluation (θ + a • s.degreePoint d) n) =
        if s.evaluation θ n = 0 then SignType.sign a else SignType.sign (s.evaluation θ n) := by
  classical
  have hrow (n : ↥(d.cutoff k \ {0})) :
      ∀ᶠ a : ℝ in nhds 0,
        SignType.sign (s.evaluation (θ + a • s.degreePoint d) n) =
          if s.evaluation θ n = 0 then SignType.sign a else SignType.sign (s.evaluation θ n) := by
    by_cases hz : s.evaluation θ n = 0
    · have hp := s.evaluation_degreePoint_pos d (d.mem_cutoff.mp n.property.1).1 n.property.2
      exact Filter.Eventually.of_forall fun a => by
        simp only [map_add, map_smul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply,
          hz, zero_add, smul_eq_mul, sign_mul, sign_pos hp, mul_one, ↓reduceIte]
    · have hc : Continuous (fun a : ℝ => s.evaluation (θ + a • s.degreePoint d) n) := by
        simp only [map_add, map_smul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply,
          smul_eq_mul]
        fun_prop
      have ht := (continuousAt_sign_of_ne_zero hz).tendsto.comp
        (by simpa using hc.tendsto 0)
      simpa only [nhds_discrete, Filter.tendsto_pure, Function.comp_def, hz, ↓reduceIte,
        map_add, map_smul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul,
        KSSpace.evaluation_degreePoint] using ht
  filter_upwards [Filter.eventually_all.mpr hrow] with a ha n hn
  exact ha ⟨n, hn⟩

end KSSpace
end Mei
