/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Polynomial.Laurent
public import Mei.RingTheory.Node.Gluing
public import Mei.RingTheory.Node.ScalarTower

/-!
# The focus-focus slab algebra

The focus-focus affine singularity has two chambers separated by the slab `u = 0`.
At order `k` its coefficients live over a ring `S` with a smoothing parameter `t`,
`t^(k+1) = 0`, typically `S = K[t]/(t^(k+1))`, and Laurent polynomials in the tangential
monomial `w`. The left chamber `S[x₁,y₁,w^{±1}]/(x₁y₁-t, y₁^(k+1))` and the right chamber
`S[x₂,y₂,w^{±1}]/(x₂y₂-t, x₂^(k+1))` are glued over their common quotient with `f = 1 + w`
inverted, by `x₁ ↦ f x₂` and `y₁ ↦ f⁻¹ y₂`. The slab coefficient algebra is the fiber product
of this cospan.

We show that the slab coefficient algebra is the nodal algebra
`S[W^{±1},X,Y]/(XY - t(1+W))`, with `X = (x₁, f x₂)`, `Y = (f y₁, y₂)` and `W = (w, w)`, and
that this algebra is free over `S` on the monomials `W^b X^d` and `W^b Y^(d+1)` for `b ∈ ℤ`
and `d ≥ 0`. The isomorphism is `Mei.NodeAlgebra.slabEquiv` over `S[w^{±1}]`, using that
`1 + w` is a nonzerodivisor modulo every power of `t`.

This is the local model of Gross–Siebert, *An invitation to toric degenerations*, §2.3,
arXiv:0808.2749v2.
-/

public section

noncomputable section

namespace Mei.FocusFocus

open TauCeti LaurentPolynomial Module

variable {S : Type*} [CommRing S] (t : S) (k : ℕ)

/-- The nodal algebra `S[W^{±1},X,Y]/(XY - t(1+W))`. -/
abbrev SlabNode : Type _ := NodeAlgebra S[T;T⁻¹] (C t * (1 + T 1))

/-- **The focus-focus slab algebra.** If `t^(k+1) = 0`, the fiber product of the two truncated
chambers over their localized overlap is `S[W^{±1},X,Y]/(XY - t(1+W))`, with `X = (x₁, f x₂)`
and `Y = (f y₁, y₂)` (`Mei.NodeAlgebra.coe_toSlabAlgebra_coord_zero` and
`Mei.NodeAlgebra.coe_toSlabAlgebra_coord_one`). -/
def algebraEquiv (ht : t ^ (k + 1) = 0) :
    SlabNode t ≃ₐ[S[T;T⁻¹]] NodeAlgebra.slabAlgebra (C t) (1 + T 1) k :=
  NodeAlgebra.slabEquiv _ (by rw [← map_pow, ht, map_zero]) fun j c h => by
    rw [← map_pow] at h ⊢
    exact C_dvd_of_C_dvd_one_add_T_mul h

/-- The focus-focus isomorphism is the general slab comparison map. -/
@[simp]
theorem algebraEquiv_apply (ht : t ^ (k + 1) = 0) (z : SlabNode t) :
    algebraEquiv t k ht z = NodeAlgebra.toSlabAlgebra (C t) (1 + T 1) k z := by
  rw [algebraEquiv, NodeAlgebra.slabEquiv_apply]

open scoped Mei.NodeAlgebra

/-- The `S`-basis of `S[W^{±1},X,Y]/(XY - t(1+W))` by the monomials `W^b X^d` and
`W^b Y^(d+1)`. -/
def basis : Basis (ℤ × (ℕ ⊕ ℕ)) S (SlabNode t) :=
  (AddMonoidAlgebra.basis ℤ S : Basis ℤ S S[T;T⁻¹]).smulTower
    (NodeAlgebra.normalFormBasis _)

/-- The basis vector at `(b, inl d)` is `W^b X^d`. -/
@[simp]
theorem basis_apply_inl (b : ℤ) (d : ℕ) :
    basis t (b, .inl d) = algebraMap S[T;T⁻¹] (SlabNode t) (T b) * NodeAlgebra.coord _ 0 ^ d := by
  rw [basis, Basis.smulTower_apply, Algebra.smul_def, NodeAlgebra.normalFormBasis_inl,
    AddMonoidAlgebra.basis_apply, single_eq_C_mul_T, map_one, one_mul]

/-- The basis vector at `(b, inr d)` is `W^b Y^(d+1)`. -/
@[simp]
theorem basis_apply_inr (b : ℤ) (d : ℕ) :
    basis t (b, .inr d) =
      algebraMap S[T;T⁻¹] (SlabNode t) (T b) * NodeAlgebra.coord _ 1 ^ (d + 1) := by
  rw [basis, Basis.smulTower_apply, Algebra.smul_def, NodeAlgebra.normalFormBasis_inr,
    AddMonoidAlgebra.basis_apply, single_eq_C_mul_T, map_one, one_mul]

/-- `S[W^{±1},X,Y]/(XY - t(1+W))` is a free `S`-module. -/
theorem free : Module.Free S (SlabNode t) :=
  .of_basis (basis t)

/-- `S[W^{±1},X,Y]/(XY - t(1+W))` is a flat `S`-module. -/
theorem flat : Module.Flat S (SlabNode t) :=
  have := free t
  inferInstance

end Mei.FocusFocus
