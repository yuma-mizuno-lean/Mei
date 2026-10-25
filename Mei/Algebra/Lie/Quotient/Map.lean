/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.Algebra.Lie.Abelian

/-!
# Maps between Lie algebra quotients

A Lie homomorphism taking an ideal into another induces a homomorphism between
quotients. `LieIdeal.mapQ` supplies this construction, its quotient square,
identity and composition laws, and its kernel and surjectivity properties. In
particular, the identity homomorphism gives the transitions in any decreasing
tower of Lie ideals.

An ideal has central image in a quotient exactly when its bracket with the whole
Lie algebra is killed. Applied to nested ideals, this characterizes when the
transition between their quotients is a central extension.

The construction follows Mathlib's `Submodule.mapQ` and uses the universal property
`LieIdeal.liftQ` in `TauCeti.Algebra.Lie.Quotient`.
-/

public section

namespace LieIdeal

variable {R L L' L'' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']

variable (I : LieIdeal R L) (J : LieIdeal R L')

/-- The Lie homomorphism induced on quotients by a map carrying `I` into `J`. -/
def mapQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) : L ⧸ I →ₗ⁅R⁆ L' ⧸ J :=
  I.liftQ (J.mkQ.comp f) (by
    intro x hx
    rw [LieHom.mem_ker, LieHom.comp_apply, mkQ_apply,
      LieSubmodule.Quotient.mk_eq_zero']
    exact h hx)

/-- The underlying linear map is Mathlib's map between module quotients. -/
theorem toLinearMap_mapQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    (I.mapQ J f h).toLinearMap =
      I.toSubmodule.mapQ J.toSubmodule f.toLinearMap (by intro x hx; exact h hx) := by
  rw [mapQ, coe_liftQ]
  rfl

/-- The induced map sends the class of `x` to the class of `f x`. -/
@[simp]
theorem mapQ_apply (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) (x : L) :
    I.mapQ J f h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk (f x) := by
  simp [mapQ, LieHom.comp_apply]

/-- The square formed by the two quotient projections commutes. -/
theorem mapQ_mkQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    (I.mapQ J f h).comp I.mkQ = J.mkQ.comp f := by
  apply LieHom.ext
  intro x
  simp [mkQ_apply]

/-- The identity induces the identity on a Lie quotient. -/
@[simp]
theorem mapQ_id (h : I ≤ I.comap (LieHom.id : L →ₗ⁅R⁆ L) := le_rfl) :
    I.mapQ I LieHom.id h = LieHom.id := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

/-- Passing to quotients respects composition of Lie homomorphisms. -/
theorem mapQ_comp (K : LieIdeal R L'') (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'')
    (hf : I ≤ J.comap f) (hg : J ≤ K.comap g)
    (hgf : I ≤ K.comap (g.comp f) := fun _ hx => hg (hf hx)) :
    I.mapQ K (g.comp f) hgf = (J.mapQ K g hg).comp (I.mapQ J f hf) := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

/-- A map between quotients making the quotient square commute exists exactly
when the original map carries the source ideal into the target ideal. -/
theorem exists_mapQ_iff (f : L →ₗ⁅R⁆ L') :
    (∃ g : L ⧸ I →ₗ⁅R⁆ L' ⧸ J, g.comp I.mkQ = J.mkQ.comp f) ↔
      I ≤ J.comap f := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    have hzero : I.mkQ x = 0 := by
      simpa only [mkQ_apply, LieSubmodule.Quotient.mk_eq_zero'] using hx
    have heq : (J.mkQ.comp f) x = 0 := by
      rw [← hg, LieHom.comp_apply, hzero, map_zero]
    rw [LieHom.comp_apply, mkQ_apply, LieSubmodule.Quotient.mk_eq_zero'] at heq
    exact mem_comap.mpr heq
  · intro h
    exact ⟨I.mapQ J f h, I.mapQ_mkQ J f h⟩

/-- The kernel on quotients is the image of the inverse image of the target ideal. -/
theorem ker_mapQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    (I.mapQ J f h).ker = (J.comap f).map I.mkQ := by
  rw [← LieSubmodule.toSubmodule_inj, LieHom.ker_toSubmodule,
    toLinearMap_mapQ, Submodule.ker_mapQ,
    coe_map_of_surjective I.surjective_mkQ]
  rfl

/-- The induced quotient map is injective exactly when the inverse image of the
target ideal contains no additional elements. -/
theorem mapQ_injective_iff (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    Function.Injective (I.mapQ J f h) ↔ J.comap f ≤ I := by
  rw [← LieHom.ker_eq_bot, ker_mapQ, LieIdeal.map_eq_bot_iff, mkQ_ker]

/-- Surjectivity of the original map implies surjectivity on quotients. -/
theorem mapQ_surjective (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f)
    (hf : Function.Surjective f) : Function.Surjective (I.mapQ J f h) :=
  I.liftQ_surjective _ _ (J.surjective_mkQ.comp hf)

section Nested

variable (I J : LieIdeal R L)

/-- The transition from the quotient by a smaller ideal to the quotient by a
larger ideal. This is the Lie algebra analogue of `Submodule.factor`. -/
def factor (h : I ≤ J) : L ⧸ I →ₗ⁅R⁆ L ⧸ J :=
  I.liftQ J.mkQ (by rw [mkQ_ker]; exact h)

/-- A quotient transition sends each representative to the same representative. -/
@[simp]
theorem factor_apply (h : I ≤ J) (x : L) :
    I.factor J h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk x := by
  simp [factor]

/-- A quotient transition at the same ideal is the identity. -/
@[simp]
theorem factor_refl : I.factor I le_rfl = LieHom.id := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

/-- Successive quotient transitions agree with the direct transition. -/
@[simp]
theorem factor_comp (K : LieIdeal R L) (hIJ : I ≤ J) (hJK : J ≤ K) :
    (J.factor K hJK).comp (I.factor J hIJ) = I.factor K (hIJ.trans hJK) := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

/-- Quotient transitions are surjective. -/
theorem factor_surjective (h : I ≤ J) : Function.Surjective (I.factor J h) :=
  I.liftQ_surjective _ _ J.surjective_mkQ

/-- The kernel of a quotient transition is the image of the larger ideal. -/
theorem ker_factor (h : I ≤ J) : (I.factor J h).ker = J.map I.mkQ := by
  exact J.ker_liftQ_mkQ _

/-- An ideal has central image in the quotient by `I` exactly when all its
brackets with the ambient algebra belong to `I`. -/
theorem map_mkQ_le_center_iff :
    J.map I.mkQ ≤ LieAlgebra.center R (L ⧸ I) ↔ ⁅(⊤ : LieIdeal R L), J⁆ ≤ I := by
  rw [LieSubmodule.lie_le_iff]
  constructor
  · intro h x _ y hy
    have hy' := h (LieIdeal.mem_map (f := I.mkQ) hy)
    rw [LieModule.mem_maxTrivSubmodule] at hy'
    have hxy := hy' (I.mkQ x)
    rw [← LieHom.map_lie, mkQ_apply, LieSubmodule.Quotient.mk_eq_zero'] at hxy
    exact hxy
  · intro h y hy
    obtain ⟨y, rfl⟩ := LieIdeal.mem_map_of_surjective I.surjective_mkQ hy
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    obtain ⟨x, rfl⟩ := I.surjective_mkQ x
    rw [← LieHom.map_lie, mkQ_apply, LieSubmodule.Quotient.mk_eq_zero']
    exact h x (LieSubmodule.mem_top x) y y.property

/-- A quotient transition is a central extension exactly when bracketing with
the larger ideal lands in the smaller ideal. -/
theorem ker_factor_le_center_iff (h : I ≤ J) :
    (I.factor J h).ker ≤ LieAlgebra.center R (L ⧸ I) ↔
      ⁅(⊤ : LieIdeal R L), J⁆ ≤ I := by
  rw [ker_factor]
  exact I.map_mkQ_le_center_iff J

end Nested

/-- Induced maps commute with the transitions obtained by enlarging the source
and target ideals. -/
theorem factor_comp_mapQ (I' : LieIdeal R L) (J' : LieIdeal R L')
    (hI : I ≤ I') (hJ : J ≤ J') (f : L →ₗ⁅R⁆ L')
    (hf : I ≤ J.comap f) (hf' : I' ≤ J'.comap f) :
    (J.factor J' hJ).comp (I.mapQ J f hf) =
      (I'.mapQ J' f hf').comp (I.factor I' hI) := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

end LieIdeal
