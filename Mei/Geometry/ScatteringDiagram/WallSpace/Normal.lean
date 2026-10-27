/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Joint
public import Mei.Algebra.Group.Hom.Int

/-!
# The wall normal of a transverse joint component

Suppose a joint tangent subgroup is the common kernel of two integral normals
`f` and `g`. For a geometric degree `v` outside that subgroup, its correction
normal is `f v • g - g v • f`. Every wall space of this degree whose normal
annihilates the joint lies in this single wall space. This does not require a
primitive choice of normal, a basis, or saturation of the positive monoid.
If the computed normal is zero, all these wall spaces are zero.

The result applies to homogeneous components of the nonlinear BCH remainder
at a joint. It complements the conditional
`DirectedWallSpaces.decompose_log_list_prod_sub_mem_wall`: here a suitable
normal is computed directly, without requiring a primitive generator of the
annihilator.

The joint-subalgebra argument is developed in
`Mei.Geometry.ScatteringDiagram.WallSpace.Joint`. The contracted-normal
calculation is the local wall-space calculation in Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, proof of Theorem 2.6.
-/

public section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommMonoid Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)

/-- Nonzero integral normals with the same kernel define the same wall spaces.
In particular a change of coorientation preserves eligible coefficients. -/
theorem wall_eq_of_ker_eq (n : Γ) {m m' : Λ →+ ℤ} (hm : m ≠ 0)
    (hker : m.ker = m'.ker) : H.wall n m = H.wall n m' := by
  obtain ⟨c, e, hc, he, hme⟩ := m.exists_ne_zero_zsmul_eq_of_ker_eq m' hm hker
  rw [← H.rescale n m c hc, hme, H.rescale n m' e he]

/-- At a degree transverse to a common kernel, the sum of all wall spaces
annihilating that kernel is the wall space with the contracted normal.
This also applies when that normal vanishes, in which case the sum is zero. -/
theorem iSup_wall_eq_wall_of_inf_ker (f g : Λ →+ ℤ) {n : Γ}
    (hn : ρ n ∉ f.ker ⊓ g.ker) :
    (⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ f.ker ⊓ g.ker, m v = 0), H.wall n m) =
      H.wall n (f (ρ n) • g - g (ρ n) • f) := by
  let μ := f (ρ n) • g - g (ρ n) • f
  apply le_antisymm
  · refine iSup_le fun m => iSup_le fun hm => ?_
    by_cases hmn : m (ρ n) = 0
    · have hker : μ.ker ≤ m.ker :=
        f.ker_zsmul_sub_zsmul_le_of_inf_ker_le g m (ρ n) hn
          (fun v hv => AddMonoidHom.mem_ker.mpr (hm v hv)) hmn
      by_cases hμ : μ = 0
      · have hm0 : m = 0 := by
          apply AddMonoidHom.ext
          intro v
          exact AddMonoidHom.mem_ker.mp (hker (by simp [hμ]))
        simp [hm0, H.zero_normal]
      · obtain ⟨c, d, hc, hcd⟩ := μ.exists_ne_zero_zsmul_eq_of_ker_le m hμ hker
        by_cases hd : d = 0
        · have hm0 : m = 0 := by
            ext v
            have heq := DFunLike.congr_fun hcd v
            have hv : c * m v = 0 := by simpa [hd] using heq
            exact (mul_eq_zero.mp hv).resolve_left hc
          simp [hm0, H.zero_normal]
        · have heq : H.wall n m = H.wall n μ := calc
            H.wall n m = H.wall n (c • m) := (H.rescale n m c hc).symm
            _ = H.wall n (d • μ) := congrArg (H.wall n) hcd
            _ = H.wall n μ := H.rescale n μ d hd
          exact heq.le
    · simp [H.nontangent n m hmn]
  · have hμW : ∀ v ∈ f.ker ⊓ g.ker, μ v = 0 := by
      intro v hv
      have hf : f v = 0 := hv.1
      have hg : g v = 0 := hv.2
      simp [μ, hf, hg]
    exact le_iSup_of_le μ (le_iSup_of_le hμW le_rfl)

variable [DecidableEq Γ] [DirectSum.Decomposition ℒ]

/-- Every component of a transverse joint element belongs to the wall space with its computed
integral normal. Components along the joint vanish, and no generation hypothesis for the
annihilator is needed. -/
theorem decompose_mem_wall_of_mem_transverseJointSubmodule_inf_ker
    (f g : Λ →+ ℤ) {x : L}
    (hx : x ∈ H.transverseJointSubmodule (f.ker ⊓ g.ker).toAddSubmonoid)
    {n : Γ} :
    (DirectSum.decompose ℒ x n : L) ∈ H.wall n (f (ρ n) • g - g (ρ n) • f) := by
  by_cases hn : ρ n ∈ f.ker ⊓ g.ker
  · rw [H.decompose_eq_zero_of_mem_transverseJointSubmodule hx hn]
    exact Submodule.zero_mem _
  · have h := H.decompose_mem_of_mem_transverseJointSubmodule
      (f.ker ⊓ g.ker).toAddSubmonoid hx n
    simpa only [AddSubgroup.mem_toAddSubmonoid, H.iSup_wall_eq_wall_of_inf_ker f g hn] using h

section BCH

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing.IsNilpotent L]

/-- In every degree, the nonlinear homogeneous part of a joint product lies in the wall space
with normal contracted against its total geometric degree. -/
theorem decompose_log_list_prod_sub_mem_wall_inf_ker
    (f g : Λ →+ ℤ) {l : List (BCHGroup L)}
    (hl : ∀ a ∈ l, a ∈ (H.jointSubalgebra (f.ker ⊓ g.ker).toAddSubmonoid).bchSubgroup)
    {n : Γ} :
    (DirectSum.decompose ℒ (BCHGroup.log l.prod - (l.map BCHGroup.log).sum) n : L) ∈
      H.wall n (f (ρ n) • g - g (ρ n) • f) :=
  H.decompose_mem_wall_of_mem_transverseJointSubmodule_inf_ker f g
    (H.log_list_prod_sub_sum_mem_transverseJointSubmodule hl)

end BCH

end Mei.DirectedWallSpaces
