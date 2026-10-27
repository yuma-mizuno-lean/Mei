/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.CosetCover

/-!
# Avoiding finite unions of subspaces in a spanning additive subgroup

An additive subgroup spanning a vector space in characteristic zero is not
contained in a finite union of proper subspaces. In particular, a common
transverse direction can be chosen inside an integral lattice, rather than
merely in the ambient vector space.

The argument applies Mathlib's `Submodule.exists_finiteIndex_of_cover`, the
submodule form of B. H. Neumann's coset-cover lemma, to the inverse images of the
subspaces. Finite index forces a positive integer multiple of every vector into
one inverse image. Characteristic zero and the spanning property then force
that subspace to be the whole space.
-/

public section

noncomputable section

namespace AddMonoidHom

variable {N K V ι : Type*} [AddCommGroup N] [DivisionRing K] [CharZero K]
  [AddCommGroup V] [Module K V]

/-- A spanning additive subgroup of a vector space in characteristic zero contains
a vector outside any finite family of proper subspaces. The additive homomorphism
need not be injective, and the vector space need not be finite-dimensional. -/
theorem exists_forall_apply_notMem_of_span_eq_top (i : N →+ V)
    (hi : Submodule.span K (Set.range i) = ⊤) [Finite ι]
    (p : ι → Submodule K V) (hp : ∀ j, p j ≠ ⊤) :
    ∃ n : N, ∀ j, i n ∉ p j := by
  classical
  let := Fintype.ofFinite ι
  let q (j : ι) : Submodule ℤ N :=
    ((p j).restrictScalars ℤ).comap i.toIntLinearMap
  by_contra! hcover
  have hq : ⋃ j ∈ Finset.univ, (q j : Set N) = Set.univ := by
    ext n
    simpa [q] using hcover n
  obtain ⟨j, _, hj⟩ := Submodule.exists_finiteIndex_of_cover hq
  apply hp j
  apply top_unique
  rw [← hi, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  obtain ⟨a, ha, _, han⟩ :=
    (q j).toAddSubgroup.exists_nsmul_mem_of_index_ne_zero hj.index_ne_zero n
  have ham : (a : K) • i n ∈ p j := by
    simpa only [q, AddSubgroup.mem_carrier, Submodule.mem_toAddSubgroup,
      Submodule.mem_comap, Submodule.restrictScalars_mem,
      AddMonoidHom.coe_toIntLinearMap, map_nsmul, Nat.cast_smul_eq_nsmul] using han
  exact ((p j).smul_mem_iff (Nat.cast_ne_zero.mpr ha.ne')).mp ham

end AddMonoidHom
