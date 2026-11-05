/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Colimit.Module

/-!
# Semilinear maps out of module direct limits

Restriction of scalars turns a compatible family of semilinear maps into
linear maps. Mathlib's direct-limit lift then gives the semilinear map and
its characteristic formula on each structure map.
-/

public section
noncomputable section

namespace Module.DirectLimit

/-- Descend compatible semilinear maps through a module direct limit. -/
def liftSemilinear {R S ι : Type*} [Semiring R] [Semiring S] [Preorder ι]
    [DecidableEq ι] {G : ι → Type*} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) {P : Type*} [AddCommMonoid P] [Module S P]
    (φ : R →+* S) (g : ∀ i, G i →ₛₗ[φ] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x) : DirectLimit G f →ₛₗ[φ] P :=
  letI := Module.compHom P φ
  let g' : ∀ i, G i →ₗ[R] P := fun i =>
    { toFun := g i, map_add' := (g i).map_add, map_smul' := (g i).map_smul' }
  let F := lift R ι G f g' hg
  { toFun := F, map_add' := F.map_add, map_smul' := F.map_smul }

/-- The semilinear lift agrees with each map of the compatible family. -/
@[simp]
theorem liftSemilinear_of {R S ι : Type*} [Semiring R] [Semiring S] [Preorder ι]
    [DecidableEq ι] {G : ι → Type*} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) {P : Type*} [AddCommMonoid P] [Module S P]
    (φ : R →+* S) (g : ∀ i, G i →ₛₗ[φ] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x) (i : ι) (x : G i) :
    liftSemilinear f φ g hg (of R ι G f i x) = g i x := by
  let := Module.compHom P φ
  let g' : ∀ i, G i →ₗ[R] P := fun i =>
    { toFun := g i, map_add' := (g i).map_add, map_smul' := (g i).map_smul' }
  exact lift_of g' hg x

end Module.DirectLimit
