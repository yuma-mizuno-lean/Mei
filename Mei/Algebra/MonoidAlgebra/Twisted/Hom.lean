/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Maps of twisted monoid algebras

A coefficient homomorphism and a monoid homomorphism induce a ring homomorphism
when they carry the source factor set to the target factor set. The map sends
each basis vector to the vector at the image exponent and applies the coefficient
homomorphism to scalars. This allows specialization of twisted coefficient algebras.

The construction uses `TauCeti.TwistedMonoidAlgebra.lift`, with scalars restricted
along the coefficient homomorphism using `Algebra.compHom`.
-/

public section

noncomputable section

namespace Mei.TwistedMonoidAlgebra

open TauCeti TauCeti.TwistedMonoidAlgebra

variable {R S G H : Type*} [CommSemiring R] [CommSemiring S] [Monoid G] [Monoid H]
  {α : G → G → Rˣ} {β : H → H → Sˣ} [IsFactorSet α] [IsFactorSet β]

/-- Change coefficients and exponents, preserving the twisting factor set. -/
def map (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j)) :
    twistedMonoidAlgebra R G α →+* twistedMonoidAlgebra S H β :=
  letI := Algebra.compHom (twistedMonoidAlgebra S H β) φ
  (lift (fun g => of (f g)) (by simp) (by
    intro g j
    rw [of_mul_of, map_mul]
    exact congrArg (fun u : Sˣ => (u : S) • (of (f g * f j) :
      twistedMonoidAlgebra S H β)) (h g j).symm)).toRingHom

/-- A twisted basis vector maps to the vector at the image exponent. -/
@[simp]
theorem map_of (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j)) (g : G) :
    map φ f h (of g) = of (f g) := by
  simp [map]

/-- The coefficient map on a twisted algebra restricts to the given scalar map. -/
@[simp]
theorem map_algebraMap (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j)) (r : R) :
    map φ f h (algebraMap R _ r) = algebraMap S _ (φ r) := by
  -- `map` is the ring map underlying `lift`, an algebra map for `Algebra.compHom`, whose
  -- `algebraMap` is by definition `algebraMap S _ ∘ φ`.
  let := Algebra.compHom (twistedMonoidAlgebra S H β) φ
  exact (lift (fun g => of (f g)) _ _).commutes r

/-- Coefficients transform semilinearly under a twisted algebra map. -/
@[simp]
theorem map_smul (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j))
    (r : R) (x : twistedMonoidAlgebra R G α) :
    map φ f h (r • x) = φ r • map φ f h x := by
  simp only [Algebra.smul_def, map_mul, map_algebraMap]

/-- Ring homomorphisms from a twisted algebra agree if they agree on scalars
and on all twisted basis vectors. -/
theorem ringHom_ext {A : Type*} [Semiring A]
    {f g : twistedMonoidAlgebra R G α →+* A}
    (hs : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hb : ∀ j, f (of j) = g (of j)) : f = g := by
  ext x
  rw [← (basis R G α).linearCombination_repr x, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, Algebra.smul_def, map_mul, basis_apply, hs, hb]

end Mei.TwistedMonoidAlgebra
