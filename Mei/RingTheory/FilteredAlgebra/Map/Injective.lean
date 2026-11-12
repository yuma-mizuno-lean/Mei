/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Map

/-!
# Injectivity of filtered completion maps

A continuous ring map induces an injective completion map when its inverse images
of target filtration ideals are cofinal in the source filtration. The finite
quotient maps need not be injective at the cutoffs used to define the map, and the
original filtrations need not be separated.
-/

public section

namespace TauCeti.AlgFiltration

variable {A B : Type*} [Ring A] [Ring B]
  (F : AlgFiltration A) (G : AlgFiltration B)
  (f : A →+* B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap f)

/-- Cofinal reflection of filtration ideals makes the induced completion map injective. -/
theorem mapCompletion_injective_of_comap_le
    (hreflect : ∀ k, ∃ j, (G.ideal (j + 1)).comap f ≤ F.ideal (k + 1)) :
    Function.Injective (F.mapCompletion G f l hl hf) := by
  suffices hzero : ∀ x, F.mapCompletion G f l hl hf x = 0 → x = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    exact hzero (x - y) (by rw [map_sub, hxy, sub_self])
  intro x hx
  apply F.completion_ext
  intro k
  obtain ⟨j, hj⟩ := hreflect k
  let m := max (l j) k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection m x)
  have hfa : f a ∈ G.ideal (j + 1) := by
    have he := congrArg (G.projection j) hx
    rw [F.projection_mapCompletion_of_le G f l hl hf j m (le_max_left _ _),
      ← ha, Ideal.quotientMap_mk, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  have haF : a ∈ F.ideal (k + 1) := hj hfa
  have he := F.factor_projection (le_max_right (l j) k) x
  rw [← ha, Ideal.Quotient.factor_mk] at he
  rw [map_zero, ← he]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr haF

end TauCeti.AlgFiltration
