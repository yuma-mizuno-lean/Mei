/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.IntegralAffine
public import Mei.Geometry.Toric.Algebraic.Lattice
public import Mei.Analysis.Convex.Exposed

/-!
# Lattice lifts and translations of integral affine equivalences

Scalar extension lifts integral linear automorphisms to zero-translation affine
automorphisms. Translations form the kernel of the projection to the lattice
automorphism group. Integral affine transport also preserves exposed subsets.
-/

public section

namespace TauCeti.Toric

/-! ### The integral affine symmetry group -/

namespace IntegralAffineEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

/-- Extend a lattice equivalence with zero translation using scalar extension. -/
noncomputable def ofLatticeEquiv (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') : IntegralAffineEquiv h h' where
  toAffineEquiv := (h.extendEquiv h' σ).toAffineEquiv
  latticeEquiv := σ
  map_lattice n :=
    (LinearMap.congr_fun (h.extendEquiv_toLinearMap h' σ) (i n)).trans
      (h.extend_apply i' σ.toAddMonoidHom n)

/-- The underlying affine equivalence is the zero-translation real extension. -/
@[simp] theorem ofLatticeEquiv_toAffineEquiv (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (σ : N ≃+ N') :
    (ofLatticeEquiv h h' σ).toAffineEquiv = (h.extendEquiv h' σ).toAffineEquiv := by rfl

/-- The zero-translation lift evaluates by the canonical real-linear extension. -/
@[simp↓] theorem ofLatticeEquiv_apply (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') (x : V) :
    ofLatticeEquiv h h' σ x = h.extend i' σ.toAddMonoidHom x :=
  congrFun (h.coe_extendEquiv h' σ) x

/-- Scalar extension preserves the specified lattice equivalence. -/
@[simp] theorem ofLatticeEquiv_latticeEquiv (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (σ : N ≃+ N') :
    (ofLatticeEquiv h h' σ).latticeEquiv = σ := by rfl

/-- Extending the identity lattice equivalence gives the identity affine equivalence. -/
@[simp] theorem ofLatticeEquiv_refl (h : IsIntegralLattice i) :
    ofLatticeEquiv h h (AddEquiv.refl N) = refl h := by
  apply toAffineEquiv_injective
  rw [ofLatticeEquiv_toAffineEquiv, refl_toAffineEquiv, h.extendEquiv_refl]
  rfl

/-- Inversion commutes with the zero-translation extension of a lattice equivalence. -/
@[simp] theorem ofLatticeEquiv_symm (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (σ : N ≃+ N') :
    (ofLatticeEquiv h h' σ).symm = ofLatticeEquiv h' h σ.symm := by
  apply toAffineEquiv_injective
  rw [symm_toAffineEquiv, ofLatticeEquiv_toAffineEquiv, ofLatticeEquiv_toAffineEquiv,
    ← h.extendEquiv_symm h' σ]
  rfl

/-- Zero-translation extension respects composition between arbitrary integral lattices. -/
@[simp] theorem ofLatticeEquiv_trans {N'' V'' : Type*} [AddCommGroup N'']
    [AddCommGroup V''] [Module ℝ V''] {i'' : N'' →+ V''}
    (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (h'' : IsIntegralLattice i'') (σ : N ≃+ N') (τ : N' ≃+ N'') :
    (ofLatticeEquiv h h' σ).trans (ofLatticeEquiv h' h'' τ) =
      ofLatticeEquiv h h'' (σ.trans τ) := by
  apply toAffineEquiv_injective
  rw [trans_toAffineEquiv, ofLatticeEquiv_toAffineEquiv, ofLatticeEquiv_toAffineEquiv,
    ofLatticeEquiv_toAffineEquiv, ← h.extendEquiv_trans h' h'' σ τ]
  rfl

variable (h : IsIntegralLattice i)

/-- Group inversion agrees with the existing inverse equivalence. -/
@[simp↓]
theorem inv_apply (e : IntegralAffineEquiv h h) (x : V) :
    e⁻¹ x = e.symm x := by rw [inv_def]

/-- Forgetting the integral data respects composition. -/
def toAffineEquivHom : IntegralAffineEquiv h h →* (V ≃ᵃ[ℝ] V) where
  toFun := toAffineEquiv
  map_one' := one_toAffineEquiv
  map_mul' := mul_toAffineEquiv

/-- The affine homomorphism keeps the given real affine equivalence. -/
@[simp] theorem toAffineEquivHom_apply (e : IntegralAffineEquiv h h) :
    toAffineEquivHom h e = e.toAffineEquiv := by rfl

/-- The lattice part of an integral affine symmetry, as a group homomorphism.
Mathlib uses an additive group for `AddAut`, so its multiplicative tag records composition. -/
def latticeHom : IntegralAffineEquiv h h →* Multiplicative (AddAut N) where
  toFun e := Multiplicative.ofAdd e.latticeEquiv
  map_one' := congrArg Multiplicative.ofAdd (one_latticeEquiv (h := h))
  map_mul' e f := congrArg Multiplicative.ofAdd (mul_latticeEquiv e f)

/-- The lattice homomorphism returns the specified integral lattice map. -/
@[simp] theorem latticeHom_apply (e : IntegralAffineEquiv h h) :
    latticeHom h e = Multiplicative.ofAdd e.latticeEquiv := by rfl

/-- The zero-translation lift is compatible with composition of lattice automorphisms. -/
noncomputable def latticeLift : Multiplicative (AddAut N) →* IntegralAffineEquiv h h where
  toFun σ := ofLatticeEquiv h h σ.toAdd
  map_one' := by
    exact ofLatticeEquiv_refl h
  map_mul' σ τ := by
    rw [mul_def]
    exact (ofLatticeEquiv_trans h h h τ.toAdd σ.toAdd).symm

/-- The lifted lattice action evaluates by scalar extension. -/
@[simp↓] theorem latticeLift_apply (σ : Multiplicative (AddAut N)) (x : V) :
    latticeLift h σ x = h.extend i σ.toAdd.toAddMonoidHom x :=
  ofLatticeEquiv_apply h h σ.toAdd x

/-- The affine projection of a lifted lattice automorphism is its zero-translation extension. -/
@[simp] theorem latticeLift_toAffineEquiv (σ : Multiplicative (AddAut N)) :
    (latticeLift h σ).toAffineEquiv = (h.extendEquiv h σ.toAdd).toAffineEquiv := by rfl

/-- The lift retains its input lattice automorphism. -/
@[simp] theorem latticeLift_latticeEquiv (σ : Multiplicative (AddAut N)) :
    (latticeLift h σ).latticeEquiv = σ.toAdd := by rfl

/-- The zero-translation lift is a section of the lattice homomorphism. -/
theorem latticeHom_latticeLift (σ : Multiplicative (AddAut N)) :
    latticeHom h (latticeLift h σ) = σ := by rfl

/-- Every integral lattice automorphism is realized by a global integral affine symmetry. -/
theorem latticeHom_surjective : Function.Surjective (latticeHom h) :=
  fun σ => ⟨latticeLift h σ, latticeHom_latticeLift h σ⟩

/-- Arbitrary real translations are integral affine symmetries.
Compatibility is imposed on the linear part, so the translation need not be integral. -/
def constVAddHom : Multiplicative V →* IntegralAffineEquiv h h where
  toFun v :=
    { toAffineEquiv := AffineEquiv.constVAdd ℝ V v.toAdd
      latticeEquiv := AddEquiv.refl N
      map_lattice _ := by rfl }
  map_one' := by
    apply toAffineEquiv_injective
    rw [one_toAffineEquiv]
    exact AffineEquiv.constVAdd_zero ℝ V
  map_mul' v w := by
    apply toAffineEquiv_injective
    rw [mul_toAffineEquiv]
    exact AffineEquiv.constVAdd_add ℝ V v.toAdd w.toAdd

/-- The translation homomorphism acts by addition of its real vector. -/
@[simp↓] theorem constVAddHom_apply (v : Multiplicative V) (x : V) :
    constVAddHom h v x = v.toAdd + x := by rfl

/-- The underlying affine equivalence is translation by the given real vector. -/
@[simp] theorem constVAddHom_toAffineEquiv (v : Multiplicative V) :
    (constVAddHom h v).toAffineEquiv = AffineEquiv.constVAdd ℝ V v.toAdd := by rfl

/-- A real translation has the identity integral linear part. -/
@[simp] theorem constVAddHom_latticeEquiv (v : Multiplicative V) :
    (constVAddHom h v).latticeEquiv = AddEquiv.refl N := by rfl

/-- Translations act trivially on the integral tangent lattice. -/
theorem latticeHom_constVAddHom (v : Multiplicative V) :
    latticeHom h (constVAddHom h v) = 1 := by rfl

/-- Different translation vectors give different integral affine symmetries. -/
theorem constVAddHom_injective : Function.Injective (constVAddHom h) := by
  intro v w he
  apply Multiplicative.toAdd.injective
  simpa only [constVAddHom_apply, add_zero] using
    congrArg (fun e : IntegralAffineEquiv h h => e 0) he

/-- Every integral affine symmetry is its canonical zero-translation lattice lift
followed by translation by its value at the origin. -/
theorem eq_constVAddHom_mul_latticeLift (e : IntegralAffineEquiv h h) :
    e = constVAddHom h (Multiplicative.ofAdd (e 0)) * latticeLift h (latticeHom h e) := by
  ext x
  rw [mul_apply, constVAddHom_apply, latticeLift_apply, latticeHom_apply]
  have he := congrFun e.toAffineEquiv.toAffineMap.decomp x
  simp only [Pi.add_apply, AffineEquiv.linear_toAffineMap] at he
  rw [e.linear_eq_extend] at he
  exact he.trans (add_comm _ _)

/-- The kernel of the lattice homomorphism consists exactly of real translations. -/
theorem ker_latticeHom : (latticeHom h).ker = (constVAddHom h).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    refine ⟨Multiplicative.ofAdd (e 0), ?_⟩
    simpa only [he, map_one, mul_one] using (eq_constVAddHom_mul_latticeLift h e).symm
  · rintro ⟨v, rfl⟩
    exact latticeHom_constVAddHom h v

end IntegralAffineEquiv

namespace IntegralAffineEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V'] [NormedSpace ℝ V] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- The bundled continuous affine equivalence evaluates as the original map. -/
@[simp]
theorem toContinuousAffineEquiv_apply (e : IntegralAffineEquiv h h') (x : V) :
    e.toContinuousAffineEquiv x = e x :=
  congrFun e.coe_toContinuousAffineEquiv x

/-- Forgetting continuity recovers the underlying affine equivalence. -/
@[simp]
theorem toContinuousAffineEquiv_toAffineEquiv (e : IntegralAffineEquiv h h') :
    e.toContinuousAffineEquiv.toAffineEquiv = e.toAffineEquiv := by
  ext x
  exact e.toContinuousAffineEquiv_apply x

end IntegralAffineEquiv

end TauCeti.Toric

namespace IsExposed

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {P F : Set V}

/-- Integral affine equivalences preserve actual exposed subsets. -/
theorem image_integralAffineEquiv (hF : IsExposed ℝ P F)
    (e : TauCeti.Toric.IntegralAffineEquiv h h') : IsExposed ℝ (e '' P) (e '' F) := by
  apply hF.image_affineEquiv e.toAffineEquiv
  simpa only [TauCeti.Toric.IntegralAffineEquiv.symm_toAffineEquiv] using e.symm.continuous

end IsExposed
