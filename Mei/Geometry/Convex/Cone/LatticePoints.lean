/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.Cone.LatticePoints

/-!
# Lattice points of cones

For a linear graph compatible with additive lattice maps, lattice points in
the graph cone are precisely the graph of the source lattice points. This
allows graph lifts to retain degree data even when the lattice homomorphism
has a kernel.
-/

public section

namespace PointedCone

variable {R N V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid N] [AddCommMonoid V] [Module R V]

/-- A graph cone has precisely the graph of the source lattice points. Only the
target lattice map must be injective; the lattice homomorphism may have a kernel. -/
theorem latticePoints_map_prod_id {M W : Type*} [AddCommMonoid M]
    [AddCommMonoid W] [Module R W] (σ : PointedCone R V)
    (i : N →+ V) (j : M →+ W) (f : N →+ M) (F : V →ₗ[R] W)
    (hf : ∀ n, F (i n) = j (f n)) (hj : Function.Injective j) :
    (σ.map (F.prod LinearMap.id)).latticePoints (j.prodMap i) =
      (σ.latticePoints i).map (f.prod (AddMonoidHom.id N)) := by
  ext ⟨m, n⟩
  simp only [mem_latticePoints, AddMonoidHom.coe_prodMap, Prod.map_apply, mem_map,
    LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply, Prod.mk.injEq,
    AddSubmonoid.mem_map, AddMonoidHom.prod_apply, AddMonoidHom.id_apply]
  constructor
  · rintro ⟨x, hx, hxm, hxn⟩
    subst x
    exact ⟨n, hx, hj ((hf n).symm.trans hxm), rfl⟩
  · rintro ⟨a, ha, ham, rfl⟩
    exact ⟨i a, ha, by rw [hf, ham], rfl⟩

end PointedCone
