/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Quiver.Path.ZeroRuns
public import Mei.LinearAlgebra.GradedModule.History.Path
public import Mei.LinearAlgebra.ModuleFiltration.Basic

/-!
# Encounter bounds for filtered propagation histories

Let every vertex `q` of a quiver carry a graded module `M q` with a decreasing filtration
`F^0 ⊇ F^1 ⊇ ⋯`, and every arrow `e : b ⟶ c` a linear map `T e : M b → M c`. A component transfer
is the map `T e` followed by the projection to a homogeneous piece of `M c`. Give every arrow a
weight `w e`, and suppose that every component transfer along `e` carries `F^k` into
`F^{k + w e}` (`Mei.ComponentTransfersRaise`). We say that the transfers raise the filtration
by `w e`, and call a step marked when `w e > 0`.

Along a path `p`, the whole homogeneous decoration of any degree history then lies in
`F^{addWeight w p}`. If the filtration of the last module vanishes in order `r`, a history with
nonzero final decoration therefore has total weight less than `r`; with weight one on the steps
that raise the filtration, it has at most `r - 1` marked steps. If moreover every stretch of
unmarked steps, whether before the first marked step, between two of them or after the last,
has at most `h` arrows, then the path has at most `r * h + r - 1` arrows, since
`length + 1 ≤ r * (h + 1)`.

## Main declarations

* `Mei.ComponentTransfersRaise`: the component transfers along each arrow `e` raise the
  filtration by `w e`.
* `Quiver.Path.homogeneousHistory_apply_mem_submodule`: a history lies in the filtration step
  given by the total weight of its path.
* `Quiver.Path.addWeight_lt_of_homogeneousHistory_ne_zero`: a nonzero history has total weight
  less than the order at which the filtration vanishes.
* `Quiver.Path.length_add_one_le_of_homogeneousHistory_ne_zero`: a nonzero history along a path
  with short zero-weight runs has bounded length.
-/

public noncomputable section

namespace Mei

universe u v w'

variable {Q : Type u} [Quiver Q] {R : Type v} [Semiring R]
  {M : Q → Type w'} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]

variable (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c) (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)] (F : ∀ q, ModuleFiltration R (M q))
  (w : ∀ {b c : Q}, (b ⟶ c) → ℕ)

/-- Every component transfer along an arrow `e`, the map `T e` followed by the projection to a
homogeneous piece, carries the `k`-th filtration step into the `(k + w e)`-th. -/
def ComponentTransfersRaise : Prop :=
  ∀ {b c : Q} (e : b ⟶ c) (i : ι c) (k : ℕ) (x : M b),
    x ∈ (F b).submodule k → homogeneousComponent (ℳ c) i (T e x) ∈ (F c).submodule (k + w e)

variable {T ℳ F w}

/-- The defining condition of `ComponentTransfersRaise`. -/
theorem componentTransfersRaise_iff :
    ComponentTransfersRaise T ℳ F w ↔
      ∀ {b c : Q} (e : b ⟶ c) (i : ι c) (k : ℕ) (x : M b),
        x ∈ (F b).submodule k →
          homogeneousComponent (ℳ c) i (T e x) ∈ (F c).submodule (k + w e) := Iff.rfl

end Mei

namespace Quiver.Path

variable {Q : Type*} [Quiver Q] {a : Q} {R : Type*} [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c}
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)] {ℳ : ∀ q, ι q → Submodule R (M q)}
  [∀ q, DirectSum.Decomposition (ℳ q)]
  {F : ∀ q, Mei.ModuleFiltration R (M q)} {w : ∀ {b c : Q}, (b ⟶ c) → ℕ}

/-- If the component transfers raise the filtration by the weights of their arrows, a degree
history along a path lies in the filtration step given by the total weight of the path. -/
theorem homogeneousHistory_apply_mem_submodule (hT : Mei.ComponentTransfersRaise T ℳ F w)
    {b : Q} (p : Path a b) (d : p.Degrees ι) (x : M a) :
    p.homogeneousHistory T ℳ d x ∈ (F b).submodule (addWeight w p) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    obtain ⟨d, i⟩ := d
    rw [homogeneousHistory_cons, LinearMap.comp_apply, LinearMap.comp_apply, addWeight_cons]
    exact hT e i _ _ (ih d)

/-- A degree history with nonzero final decoration has total weight less than any order `r` at
which the filtration of the last module vanishes. With weight one on the steps that raise the
filtration and zero elsewhere, this bounds the number of marked steps by `r - 1`. -/
theorem addWeight_lt_of_homogeneousHistory_ne_zero (hT : Mei.ComponentTransfersRaise T ℳ F w)
    {b : Q} {p : Path a b} {d : p.Degrees ι} {x : M a} {r : ℕ}
    (hr : (F b).submodule r = ⊥) (hne : p.homogeneousHistory T ℳ d x ≠ 0) :
    addWeight w p < r := by
  by_contra hlt
  have hmem := (F b).antitone (not_lt.mp hlt) (homogeneousHistory_apply_mem_submodule hT p d x)
  rw [hr] at hmem
  exact hne ((Submodule.mem_bot R).mp hmem)

/-- A degree history with nonzero final decoration along a path whose zero-weight runs have at most
`h` arrows has at most `r * h + r - 1` arrows, where `r` is an order at which the filtration of
the last module vanishes. -/
theorem length_add_one_le_of_homogeneousHistory_ne_zero
    (hT : Mei.ComponentTransfersRaise T ℳ F w) {b : Q} {p : Path a b} {d : p.Degrees ι} {x : M a}
    {r h : ℕ} (hr : (F b).submodule r = ⊥) (hne : p.homogeneousHistory T ℳ d x ≠ 0)
    (hp : IsZeroRunBounded w h p) : p.length + 1 ≤ r * (h + 1) :=
  (length_add_one_le_of_isZeroRunBounded hp).trans
    (Nat.mul_le_mul_right _ (addWeight_lt_of_homogeneousHistory_ne_zero hT hr hne))

end Quiver.Path
