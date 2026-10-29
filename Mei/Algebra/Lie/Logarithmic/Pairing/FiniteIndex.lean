/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Basic
public import Mei.LinearAlgebra.Dual.FiniteIndex

/-!
# Tropical pairings from finite-index lattice embeddings

An injective finite-index map of tangent groups transports rational characters
by its inverse dual. Together with a compatible positive degree map, this gives
a tropical pairing on any chosen character subspace, retaining the given cutoff
modulus. In the identity-projection case the degree map itself is the tangent
map. The existing `TropicalPairing.gradedLieHom` then transports positive tangent
fields, and the coefficient and completion APIs intertwine their actions.

We use `AddMonoidHom.rationalDualEquiv` for character extension and the existing
pairing construction for the Lie maps. The character normalization follows
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.TropicalPairing

variable {R Γ Λ Γ' Λ' : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommMonoid Γ] [AddCommGroup Λ] [AddCommMonoid Γ'] [AddCommGroup Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}

/-- A finite-index tangent embedding gives a tropical pairing by extending
characters through its rational inverse dual. Compatibility is needed only on
allowed degrees; the positive degree map supplies the cutoff modulus. -/
def ofFiniteIndex (T : PositiveDegreeMap d e) (t : Λ →+ Λ')
    (ht : Function.Injective t) [t.range.FiniteIndex]
    (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n))
    (U : Submodule R (Λ →+ R)) : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U where
  degreeMap := T
  characterMap := (t.rationalDualEquiv ht).toLinearMap.comp U.subtype
  eval_eq m n hn := by simp [hρ n hn]

@[simp]
theorem ofFiniteIndex_degreeMap (T : PositiveDegreeMap d e) (t : Λ →+ Λ')
    (ht : Function.Injective t) [t.range.FiniteIndex]
    (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n)) (U : Submodule R (Λ →+ R)) :
    (ofFiniteIndex T t ht hρ U).degreeMap = T := (rfl)

@[simp]
theorem ofFiniteIndex_characterMap (T : PositiveDegreeMap d e) (t : Λ →+ Λ')
    (ht : Function.Injective t) [t.range.FiniteIndex]
    (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n)) (U : Submodule R (Λ →+ R))
    (m : U) :
    (ofFiniteIndex T t ht hρ U).characterMap m = t.rationalDualEquiv ht m.val := (rfl)

/-- The inverse dual is injective on the selected character subspace. In particular,
formal nonzero normals remain nonzero after transport. -/
theorem ofFiniteIndex_characterMap_injective (T : PositiveDegreeMap d e) (t : Λ →+ Λ')
    (ht : Function.Injective t) [t.range.FiniteIndex]
    (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n)) (U : Submodule R (Λ →+ R)) :
    Function.Injective (ofFiniteIndex T t ht hρ U).characterMap :=
  (t.rationalDualEquiv (R := R) ht).injective.comp U.subtype_injective

section IdentityProjection

variable {N N' : Type*} [AddCommGroup N] [AddCommGroup N']
  {d : PositiveDegrees N} {e : PositiveDegrees N'}

/-- For identity spatial projections, an injective positive degree map with
finite-index image is a tropical pairing with its rational inverse dual. -/
def ofFiniteIndexDegreeMap (T : PositiveDegreeMap d e) (hT : Function.Injective T)
    [T.toAddMonoidHom.range.FiniteIndex] (U : Submodule R (N →+ R)) :
    TropicalPairing (d := d) (e := e) (ρ := AddMonoidHom.id N) (ρ' := AddMonoidHom.id N') U :=
  ofFiniteIndex T T.toAddMonoidHom hT (fun _ _ => rfl) U

@[simp]
theorem ofFiniteIndexDegreeMap_degreeMap (T : PositiveDegreeMap d e)
    (hT : Function.Injective T) [T.toAddMonoidHom.range.FiniteIndex]
    (U : Submodule R (N →+ R)) :
    (ofFiniteIndexDegreeMap T hT U).degreeMap = T := (rfl)

@[simp]
theorem ofFiniteIndexDegreeMap_characterMap (T : PositiveDegreeMap d e)
    (hT : Function.Injective T) [T.toAddMonoidHom.range.FiniteIndex]
    (U : Submodule R (N →+ R)) (m : U) :
    (ofFiniteIndexDegreeMap T hT U).characterMap m =
      T.toAddMonoidHom.rationalDualEquiv hT m.val := (rfl)

end IdentityProjection

end Mei.TropicalPairing
