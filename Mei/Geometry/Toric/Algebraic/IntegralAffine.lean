/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Toric.Algebraic.RationalFunctional
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Integral affine equivalences

An integral affine equivalence is a real affine equivalence together with an
isomorphism of the integral lattices compatible with its linear part. Its
translation is arbitrary. Both directions pull rational functionals back to
rational functionals. In normed spaces the integral lattice supplies finite
dimensionality and hence continuity without further assumptions.
-/

public section

namespace Mei.Toric

open TauCeti.Toric

section Algebra

variable {N N' N'' V V' V'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

/-- An affine equivalence whose linear part identifies the integral lattices. -/
structure IntegralAffineEquiv (h : IsIntegralLattice i) (h' : IsIntegralLattice i') where
  /-- The underlying real affine equivalence, with arbitrary translation. -/
  toAffineEquiv : V ≃ᵃ[ℝ] V'
  /-- The isomorphism of the integral vectors. -/
  latticeEquiv : N ≃+ N'
  /-- Compatibility concerns the linear part, not the translated lattice points. -/
  map_lattice : ∀ n, toAffineEquiv.linear (i n) = i' (latticeEquiv n)

namespace IntegralAffineEquiv

variable {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}
  {h'' : IsIntegralLattice i''}

instance : CoeFun (IntegralAffineEquiv h h') (fun _ => V → V') :=
  ⟨fun e => e.toAffineEquiv⟩

/-- Equality of the underlying affine and lattice equivalences gives equality. -/
@[ext (iff := false)]
theorem ext {e f : IntegralAffineEquiv h h'}
    (ha : e.toAffineEquiv = f.toAffineEquiv) (hl : e.latticeEquiv = f.latticeEquiv) :
    e = f := by
  cases e
  cases f
  cases ha
  cases hl
  rfl

/-- The identity preserves the integral lattice. -/
@[expose] def refl (h : IsIntegralLattice i) : IntegralAffineEquiv h h where
  toAffineEquiv := AffineEquiv.refl ℝ V
  latticeEquiv := AddEquiv.refl N
  map_lattice _ := rfl

/-- Inverting the affine and integral equivalences preserves compatibility. -/
@[expose] def symm (e : IntegralAffineEquiv h h') : IntegralAffineEquiv h' h where
  toAffineEquiv := e.toAffineEquiv.symm
  latticeEquiv := e.latticeEquiv.symm
  map_lattice n := by
    apply e.toAffineEquiv.linear.injective
    simp [e.map_lattice]

/-- Compose integral affine equivalences, applying the left one first. -/
@[expose] def trans (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') :
    IntegralAffineEquiv h h'' where
  toAffineEquiv := e.toAffineEquiv.trans f.toAffineEquiv
  latticeEquiv := e.latticeEquiv.trans f.latticeEquiv
  map_lattice n := by
    change f.toAffineEquiv.linear (e.toAffineEquiv.linear (i n)) = _
    rw [e.map_lattice, f.map_lattice]
    rfl

/-- The identity acts as the identity on points. -/
@[simp]
theorem refl_apply (h : IsIntegralLattice i) (x : V) : refl h x = x := rfl

/-- Composition agrees with function composition. -/
@[simp]
theorem trans_apply (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') (x : V) :
    e.trans f x = f (e x) := rfl

/-- Applying the inverse after the original map recovers a point. -/
@[simp]
theorem symm_apply_apply (e : IntegralAffineEquiv h h') (x : V) : e.symm (e x) = x :=
  e.toAffineEquiv.symm_apply_apply x

/-- Applying the original map after its inverse recovers a point. -/
@[simp]
theorem apply_symm_apply (e : IntegralAffineEquiv h h') (x : V') : e (e.symm x) = x :=
  e.toAffineEquiv.apply_symm_apply x

/-- Inverting twice recovers the integral affine equivalence. -/
@[simp]
theorem symm_symm (e : IntegralAffineEquiv h h') : e.symm.symm = e := by
  apply ext <;> rfl

/-- Composition with the identity on the target changes nothing. -/
@[simp]
theorem trans_refl (e : IntegralAffineEquiv h h') : e.trans (refl h') = e := by
  apply ext
  · simp [trans, refl]
  · exact AddEquiv.ext fun _ => rfl

/-- Composition with the identity on the source changes nothing. -/
@[simp]
theorem refl_trans (e : IntegralAffineEquiv h h') : (refl h).trans e = e := by
  apply ext
  · simp [trans, refl]
  · exact AddEquiv.ext fun _ => rfl

/-- Composition with the inverse on the right gives the source identity. -/
@[simp]
theorem self_trans_symm (e : IntegralAffineEquiv h h') : e.trans e.symm = refl h := by
  apply ext <;> simp [trans, symm, refl]

/-- Composition with the inverse on the left gives the target identity. -/
@[simp]
theorem symm_trans_self (e : IntegralAffineEquiv h h') : e.symm.trans e = refl h' := by
  apply ext <;> simp [trans, symm, refl]

/-- Composition of integral affine equivalences is associative. -/
theorem trans_assoc {N''' V''' : Type*} [AddCommGroup N'''] [AddCommGroup V''']
    [Module ℝ V'''] {i''' : N''' →+ V'''} {h''' : IsIntegralLattice i'''}
    (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'')
    (g : IntegralAffineEquiv h'' h''') :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply ext <;> rfl

/-- The linear part is rational relative to the given integral lattices. -/
theorem isRationalLinearMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toAffineEquiv.linear.toLinearMap :=
  .of_integral_compatible h h' e.latticeEquiv.toAddMonoidHom
    e.toAffineEquiv.linear.toLinearMap e.map_lattice

end IntegralAffineEquiv

end Algebra

namespace IntegralAffineEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V'] [NormedSpace ℝ V] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- Continuity follows from the finite dimensionality supplied by the lattice. -/
theorem continuous (e : IntegralAffineEquiv h h') : Continuous e := by
  let := h.finiteDimensional
  exact e.toAffineEquiv.continuous_of_finiteDimensional

/-- The underlying continuous affine map used to transport affine inequalities. -/
@[expose] def toContinuousAffineMap (e : IntegralAffineEquiv h h') : V →ᴬ[ℝ] V' :=
  { e.toAffineEquiv.toAffineMap with cont := e.continuous }

/-- Bundling continuity does not change evaluation. -/
@[simp]
theorem toContinuousAffineMap_apply (e : IntegralAffineEquiv h h') (x : V) :
    e.toContinuousAffineMap x = e x := rfl

/-- Forgetting continuity gives the original affine map. -/
@[simp]
theorem toContinuousAffineMap_toAffineMap (e : IntegralAffineEquiv h h') :
    e.toContinuousAffineMap.toAffineMap = e.toAffineEquiv.toAffineMap := rfl

/-- The continuous affine map has the original rational linear part. -/
@[simp]
theorem toContinuousAffineMap_linear (e : IntegralAffineEquiv h h') :
    e.toContinuousAffineMap.toAffineMap.linear = e.toAffineEquiv.linear.toLinearMap := rfl

/-- Rationality with the exact bundled continuous-map type, for use in public
constructions without relying on unfolding the rational-map predicate. -/
theorem isRational_toContinuousAffineMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toContinuousAffineMap.toAffineMap.linear := by
  rw [toContinuousAffineMap_linear]
  exact e.isRationalLinearMap

end IntegralAffineEquiv

end Mei.Toric
