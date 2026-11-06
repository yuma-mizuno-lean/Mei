/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Recursion

/-!
# Raising endomorphisms at finite filtration order

Fix a decreasing module filtration `F` and an order `k`. An endomorphism `u` of the
order-`k` quotient `F.quotient k` *raises* the filtration when it sends the image of
`F.submodule b` into the image of `F.submodule (b + 1)` for every `b`. Such an
endomorphism is nilpotent with `u ^ (k + 1) = 0`: `k + 1` applications exhaust the
retained orders.

The typical source is the difference between an endomorphism and the identity.
`IsRaisingEnd` is closed under addition, negation and composition, so an endomorphism
that is the identity modulo a raising endomorphism stays so under products. This is the
shape of a sequence of wall crossings: each factor is the identity plus a
filtration-raising correction, and a word of them is again the identity plus a raising
endomorphism.

For an adapted endomorphism `e` the *backward* operator is `U = 1 - e`. It raises the
filtration, so `U ^ (k + 1) = 0`, and:

* the backward recursion `x = a + U x` has the unique solution `∑ j < k + 1, U ^ j a`
  (the shared semimodule theorem of `Mei.LinearAlgebra.End.Recursion`);
* every adapted linear equivalence satisfies `e.symm = ∑ j < k + 1, U ^ j`.

Both statements are what the backward-ray recursions of `Mei.ModuleProbe` consume: the
correction terms are read at strictly lower relative degree, so the recursion terminates
after `k + 1` steps and its solution is the finite geometric series of the backward
operator. No separatedness, completeness, freeness or characteristic-zero hypothesis is
used.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

section Image

variable (F : ModuleFiltration R M)

/-- The image of the order-`b` filtration term in the order-`k` quotient. -/
def quotientImage (k b : ℕ) : Submodule R (F.quotient k) :=
  (F.submodule b).map (Submodule.mkQ (F.submodule (k + 1)))

theorem mem_quotientImage {k b : ℕ} {x : F.quotient k} :
    x ∈ F.quotientImage k b ↔
      ∃ m ∈ F.submodule b, (Submodule.mkQ (F.submodule (k + 1)) m : F.quotient k) = x :=
  Submodule.mem_map

@[simp]
theorem quotientImage_zero (k : ℕ) : F.quotientImage k 0 = ⊤ := by
  rw [quotientImage, F.zero_eq_top, Submodule.map_top, Submodule.range_mkQ]

/-- The images of the filtration terms in a quotient are decreasing. -/
theorem quotientImage_antitone (k : ℕ) : Antitone (F.quotientImage k) :=
  fun _ _ hab => Submodule.map_mono (F.antitone hab)

theorem quotientImage_succ_le (k b : ℕ) : F.quotientImage k (b + 1) ≤ F.quotientImage k b :=
  F.quotientImage_antitone k (Nat.le_succ b)

/-- The order-`k + 1` term vanishes in the order-`k` quotient. -/
@[simp]
theorem quotientImage_self_eq_bot (k : ℕ) : F.quotientImage k (k + 1) = ⊥ :=
  Submodule.mkQ_map_self (F.submodule (k + 1))

/-- A transition kills exactly the classes represented by the finer filtration term. -/
theorem mem_ker_transition_iff {k l : ℕ} (h : k ≤ l) {z : M} :
    F.transition h ((F.submodule (l + 1)).mkQ z) = 0 ↔ z ∈ F.submodule (k + 1) := by
  rw [Submodule.mkQ_apply, F.transition_mk h z]
  exact Submodule.Quotient.mk_eq_zero (F.submodule (k + 1))

/-- The kernel of a quotient transition is the image of the finer term. -/
theorem ker_transition {k l : ℕ} (h : k ≤ l) :
    LinearMap.ker (F.transition h) = F.quotientImage l (k + 1) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
    exact ⟨z, (F.mem_ker_transition_iff h).mp hx, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    exact (F.mem_ker_transition_iff h).mpr hz

end Image

section Raising

variable {F : ModuleFiltration R M}

/-- An endomorphism of the order-`k` quotient raises the filtration when it sends the
image of every filtration term into the image of the next one. -/
def IsRaisingEnd (k : ℕ) (u : Module.End R (F.quotient k)) : Prop :=
  ∀ b : ℕ, F.quotientImage k b ≤ (F.quotientImage k (b + 1)).comap u

/-- Component form of the definition of a raising endomorphism. -/
theorem isRaisingEnd_iff {k : ℕ} {u : Module.End R (F.quotient k)} :
    F.IsRaisingEnd k u ↔ ∀ (b : ℕ) (x : F.quotient k), x ∈ F.quotientImage k b →
      u x ∈ F.quotientImage k (b + 1) := by
  constructor
  · intro h b x hx; exact Submodule.mem_comap.mp (h b hx)
  · intro h b x hx; exact Submodule.mem_comap.mpr (h b x hx)

namespace IsRaisingEnd

variable {k : ℕ} {u v : Module.End R (F.quotient k)}

theorem map_mem (hu : F.IsRaisingEnd k u) {b : ℕ} {x : F.quotient k}
    (hx : x ∈ F.quotientImage k b) : u x ∈ F.quotientImage k (b + 1) :=
  Submodule.mem_comap.mp (hu b hx)

theorem pow_apply_mem (hu : F.IsRaisingEnd k u) (n b : ℕ) {x : F.quotient k}
    (hx : x ∈ F.quotientImage k b) : (u ^ n) x ∈ F.quotientImage k (b + n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have h1 : (u ^ (n + 1)) x = u ((u ^ n) x) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [h1]
    exact hu.map_mem ih

/-- A filtration-raising endomorphism of the order-`k` quotient is nilpotent with the
`(k + 1)`st power zero. -/
theorem pow_eq_zero (hu : F.IsRaisingEnd k u) : u ^ (k + 1) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective x
  have h0 : (F.submodule (k + 1)).mkQ m ∈ F.quotientImage k 0 := by
    rw [F.quotientImage_zero]; exact Submodule.mem_top
  have hmem := hu.pow_apply_mem (k + 1) 0 h0
  rw [Nat.zero_add, F.quotientImage_self_eq_bot] at hmem
  exact (Submodule.mem_bot (R := R)).mp hmem

theorem neg (hu : F.IsRaisingEnd k u) : F.IsRaisingEnd k (-u) := by
  intro b x hx
  have h := Submodule.neg_mem (F.quotientImage k (b + 1)) (hu.map_mem hx)
  simpa using h

theorem add (hu : F.IsRaisingEnd k u) (hv : F.IsRaisingEnd k v) : F.IsRaisingEnd k (u + v) := by
  intro b x hx
  have h := Submodule.add_mem (F.quotientImage k (b + 1)) (hu.map_mem hx) (hv.map_mem hx)
  simpa using h

theorem sub (hu : F.IsRaisingEnd k u) (hv : F.IsRaisingEnd k v) : F.IsRaisingEnd k (u - v) := by
  have h := hu.add hv.neg
  simpa only [sub_eq_add_neg] using h

theorem mul (hu : F.IsRaisingEnd k u) (hv : F.IsRaisingEnd k v) : F.IsRaisingEnd k (u * v) := by
  intro b x hx
  have h3 := F.quotientImage_succ_le k (b + 1) (hu.map_mem (hv.map_mem hx))
  exact Submodule.mem_comap.mpr (by simpa only [Module.End.mul_apply] using h3)

end IsRaisingEnd

/-- The raising part of an endomorphism: its difference from the identity. -/
def raisingPart {k : ℕ} (e : Module.End R (F.quotient k)) : Module.End R (F.quotient k) :=
  e - 1

theorem raisingPart_apply {k : ℕ} (e : Module.End R (F.quotient k)) (x : F.quotient k) :
    F.raisingPart e x = e x - x := by
  rw [raisingPart, LinearMap.sub_apply, Module.End.one_apply]

/-- An endomorphism whose difference from the identity raises the filtration. -/
def IsAdapted (k : ℕ) (e : Module.End R (F.quotient k)) : Prop :=
  F.IsRaisingEnd k (F.raisingPart e)

/-- Being adapted is exactly the raising of the difference from the identity. -/
theorem isAdapted_iff {k : ℕ} {e : Module.End R (F.quotient k)} :
    F.IsAdapted k e ↔ F.IsRaisingEnd k (F.raisingPart e) :=
  Iff.rfl

/-- The backward-ray operator of an endomorphism: the negative of its raising part. -/
def backwardPart {k : ℕ} (e : Module.End R (F.quotient k)) : Module.End R (F.quotient k) :=
  1 - e

theorem backwardPart_apply {k : ℕ} (e : Module.End R (F.quotient k)) (x : F.quotient k) :
    F.backwardPart e x = x - e x := by
  rw [backwardPart, LinearMap.sub_apply, Module.End.one_apply]

theorem backwardPart_eq_neg_raisingPart {k : ℕ} (e : Module.End R (F.quotient k)) :
    F.backwardPart e = -F.raisingPart e := by
  rw [backwardPart, raisingPart]; abel

namespace IsAdapted

variable {k : ℕ} {e e' : Module.End R (F.quotient k)}

theorem one : F.IsAdapted k 1 := by
  intro b x _
  have h : F.raisingPart (1 : Module.End R (F.quotient k)) x = 0 := by
    rw [raisingPart_apply, Module.End.one_apply, sub_self]
  rw [Submodule.mem_comap, h]
  exact Submodule.zero_mem _

theorem mul (he : F.IsAdapted k e) (he' : F.IsAdapted k e') : F.IsAdapted k (e * e') := by
  have hsplit : F.raisingPart (e * e') =
      F.raisingPart e + F.raisingPart e' + F.raisingPart e * F.raisingPart e' := by
    simp only [raisingPart, mul_sub, sub_mul, one_mul, mul_one]
    abel
  have he1 : F.IsRaisingEnd k (F.raisingPart e) := he
  have he2 : F.IsRaisingEnd k (F.raisingPart e') := he'
  change F.IsRaisingEnd k (F.raisingPart (e * e'))
  rw [hsplit]
  exact IsRaisingEnd.add (IsRaisingEnd.add he1 he2) (IsRaisingEnd.mul he1 he2)

/-- The backward operator of an adapted endomorphism raises the filtration. -/
theorem isRaisingEnd_backwardPart (he : F.IsAdapted k e) :
    F.IsRaisingEnd k (F.backwardPart e) := by
  rw [backwardPart_eq_neg_raisingPart]
  exact IsRaisingEnd.neg he

/-- The `(k + 1)`st power of the backward operator of an adapted endomorphism vanishes. -/
theorem backwardPart_pow_eq_zero (he : F.IsAdapted k e) :
    (F.backwardPart e) ^ (k + 1) = 0 :=
  he.isRaisingEnd_backwardPart.pow_eq_zero

/-- Every solution of the backward recursion `x = a + U x` for an adapted endomorphism is
the finite sum of the iterates of the backward operator. -/
theorem eq_sum_of_eq_add (he : F.IsAdapted k e) {a x : F.quotient k}
    (hx : x = a + F.backwardPart e x) :
    x = ∑ j ∈ Finset.range (k + 1), ((F.backwardPart e) ^ j) a :=
  (Module.End.eq_finiteRecursion_of_eq_add (F.backwardPart e)
    he.backwardPart_pow_eq_zero hx).trans
    (Module.End.finiteRecursion_apply _ _ _)

end IsAdapted

/-- The inverse of an adapted linear equivalence is the finite recursion operator of its
backward operator. -/
theorem symm_eq_finiteRecursion {k : ℕ} (e : F.quotient k ≃ₗ[R] F.quotient k)
    (he : F.IsAdapted k (e : Module.End R (F.quotient k))) :
    ((e.symm : F.quotient k ≃ₗ[R] F.quotient k) : Module.End R (F.quotient k)) =
      (F.backwardPart (e : Module.End R (F.quotient k))).finiteRecursion (k + 1) := by
  apply LinearMap.ext
  intro a
  have hstep : e.symm a = a + F.backwardPart (e : Module.End R (F.quotient k)) (e.symm a) := by
    rw [backwardPart_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    abel
  exact Module.End.eq_finiteRecursion_of_eq_add (F.backwardPart (e : Module.End R (F.quotient k)))
    he.backwardPart_pow_eq_zero hstep

/-- The inverse of an adapted linear equivalence is the finite geometric series of its
backward operator. -/
theorem symm_apply_eq_sum {k : ℕ} (e : F.quotient k ≃ₗ[R] F.quotient k)
    (he : F.IsAdapted k (e : Module.End R (F.quotient k))) (a : F.quotient k) :
    e.symm a =
      ∑ j ∈ Finset.range (k + 1), ((F.backwardPart (e : Module.End R (F.quotient k))) ^ j) a :=
  (LinearMap.congr_fun (F.symm_eq_finiteRecursion e he) a).trans
    (Module.End.finiteRecursion_apply _ _ _)

end Raising

end Mei.ModuleFiltration
