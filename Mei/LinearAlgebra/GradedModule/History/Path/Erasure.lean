/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Path.Identity

/-!
# Erasing encounters that fix a homogeneous decoration

A loop between two propagation blocks can be erased when its whole output
decoration equals its whole input decoration. The arrow need not act as the
identity on other coefficients. Nonvanishing of the final history forces the
two degrees at this encounter to agree. Erasure preserves the entire final
coefficient. The degree equality identifies encounters that can be contracted
without discarding a genuine change of homogeneous piece.
-/

public noncomputable section

namespace Quiver.Path

variable {Q : Type*} [Quiver Q] {ι : Q → Type*} {a b : Q}
  (p : Path a b) (e : b ⟶ b)

variable (i₀ : ι a)

variable {R : Type*} [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {u v : Q}, (u ⟶ v) → M u →ₗ[R] M v)
  [∀ q, DecidableEq (ι q)]
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]

/-- Erasing an encounter with equal whole input and output decorations
preserves the final coefficient through every later transfer. -/
theorem homogeneousHistory_degreesErase_of_eq {c : Q} (q : Path b c)
    (d : ((p.cons e).comp q).Degrees ι) (x : M a)
    (hfix : (p.cons e).homogeneousHistory T ℳ (degreesComp (ι := ι) (p.cons e) q d).1 x =
      p.homogeneousHistory T ℳ (degreesComp (ι := ι) (p.cons e) q d).1.1 x) :
    (p.comp q).homogeneousHistory T ℳ (degreesErase p q e d) x =
      ((p.cons e).comp q).homogeneousHistory T ℳ d x := by
  have hleft := homogeneousHistory_comp T ℳ p q
    (degreesComp (ι := ι) (p.cons e) q d).1.1
    (degreesComp (ι := ι) (p.cons e) q d).2
  have hright := homogeneousHistory_comp T ℳ (p.cons e) q
    (degreesComp (ι := ι) (p.cons e) q d).1
    (degreesComp (ι := ι) (p.cons e) q d).2
  have herase : degreesErase p q e d = (degreesComp (ι := ι) p q).symm
      ((degreesComp (ι := ι) (p.cons e) q d).1.1,
        (degreesComp (ι := ι) (p.cons e) q d).2) := by
    apply (degreesComp (ι := ι) p q).injective
    simp only [degreesComp_degreesErase, Equiv.apply_symm_apply]
  rw [herase, LinearMap.congr_fun hleft,
    ← (degreesComp (ι := ι) (p.cons e) q).symm_apply_apply d,
    LinearMap.congr_fun hright]
  simp only [Equiv.apply_symm_apply, LinearMap.comp_apply, hfix]

/-- Erasing an identity arrow from a surviving history keeps its whole output. -/
theorem homogeneousHistory_degreesErase (p : Path a b) {c : Q} (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a)
    (d : ((p.cons e).comp q).Degrees ι)
    {x : M a} (hx : x ∈ ℳ a i)
    (hd : ((p.cons e).comp q).homogeneousHistory T ℳ d x ≠ 0) :
    (p.comp q).homogeneousHistory T ℳ (degreesErase p q e d) x =
      ((p.cons e).comp q).homogeneousHistory T ℳ d x :=
  homogeneousHistory_degreesErase_of_eq p e T ℳ q d x
    (homogeneousHistory_loop_eq_of_eq_id T ℳ p q e he i d hx hd)

/-- In a surviving homogeneous history, equal whole decorations at a loop
force its selected degree to be the incoming degree. -/
theorem erased_degree_eq_of_decoration_eq {c : Q} (q : Path b c)
    (d : ((p.cons e).comp q).Degrees ι) (x : ℳ a i₀)
    (hfix : (p.cons e).homogeneousHistory T ℳ (degreesComp (ι := ι) (p.cons e) q d).1 x =
      p.homogeneousHistory T ℳ (degreesComp (ι := ι) (p.cons e) q d).1.1 x)
    (hne : ((p.cons e).comp q).homogeneousHistory T ℳ d x ≠ 0) :
    (degreesComp (ι := ι) (p.cons e) q d).1.2 =
      Degrees.terminalDegree i₀ p (degreesComp (ι := ι) (p.cons e) q d).1.1 := by
  have hp : (p.cons e).homogeneousHistory T ℳ (degreesComp (ι := ι) (p.cons e) q d).1 x ≠ 0 := by
    intro hz
    apply hne
    rw [← (degreesComp (ι := ι) (p.cons e) q).symm_apply_apply d, homogeneousHistory_comp,
      LinearMap.comp_apply, hz, map_zero]
  apply DirectSum.degree_eq_of_mem_mem (ℳ b)
    (homogeneousHistory_mem_vertex (T := T) (ℳ := ℳ) (p.cons e) _ i₀ x x.property)
    ?_ hp
  rw [hfix]
  exact homogeneousHistory_mem_vertex (T := T) (ℳ := ℳ) p _ i₀ x x.property

end Quiver.Path
