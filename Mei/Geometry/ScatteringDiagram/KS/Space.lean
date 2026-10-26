/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mei.Analysis.Convex.Sign
public import Mei.Geometry.Toric.Algebraic.DualLattice

/-!
# Real dual models for scattering diagrams

A `KSSpace` identifies a real vector space carrying the integral dual lattice
with the real characters of the degree group. Its evaluation normals are the
real extensions of integral evaluation. The degree functional gives a point
strictly on the positive side of every allowed-degree hyperplane.

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

end KSSpace
end Mei
