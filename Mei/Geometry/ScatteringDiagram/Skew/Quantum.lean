/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Quantum.Basic

/-!
# Quantum forms of skew lattice data

For a skew lattice datum whose form `{,}` is integral on the whole lattice, the quantum
coefficients use the integral alternating form `β(n,n') = {n',n}`
(`SkewLatticeDatum.quantumForm`), so `β(n,-)` is the integral functional `{-,n}`
(`SkewLatticeDatum.cast_quantumForm_apply`). For an unfrozen degree `n`, this functional has the
kernel of the normalized normal `{-, κ(n) n}` (`SkewLatticeDatum.ker_quantumForm`), where `κ` is
the ray index of `N°`. Hence over a nontrivial coefficient ring the quantum wall space of degree
`n` and normal `m` is nonzero exactly when `m` is nonzero with the kernel of `{-, κ(n) n}`
(`SkewLatticeDatum.wallSubmodule_quantumForm_ne_bot_iff`): the eligible quantum normals of an
unfrozen degree are the directed normals of the skew datum, up to nonzero rational multiples.

We use `SkewLatticeDatum.integralCharacter`, `SkewLatticeDatum.normal` and
`QuantumMonoidAlgebra.wallSubmodule_ne_bot_iff`. The quantum form of a skew datum follows
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(iii), arXiv:1503.06183v5, and the normals follow Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N : Type*} [AddCommGroup N] (D : SkewLatticeDatum N)
  (hD : ∀ a b, ∃ k : ℤ, D.form a b = k)

/-- The integral alternating form `β(n,n') = {n',n}` of the quantum coefficients of a skew
datum whose form is integral on the whole lattice. -/
def quantumForm : LinearMap.BilinForm ℤ N :=
  (D.integralCharacter hD).flip

/-- The quantum form pairs `n` and `n'` to `{n',n}`. -/
@[simp]
theorem cast_quantumForm_apply (n n' : N) : (D.quantumForm hD n n' : ℚ) = D.form n' n := by
  simp [quantumForm]

/-- The quantum form is alternating. -/
theorem isAlt_quantumForm : (D.quantumForm hD).IsAlt := fun n => by
  apply Int.cast_injective (α := ℚ)
  simp

variable [Module.Free ℤ N]

/-- For an unfrozen degree `n`, the functional `β(n,-) = {-,n}` has the kernel of the
normalized normal `{-, κ(n) n}`. -/
theorem ker_quantumForm {n : N} (hn : n ∈ D.unfrozen) :
    (D.quantumForm hD n).toAddMonoidHom.ker = (D.normal n hn).toAddMonoidHom.ker := by
  ext a
  have h₁ : D.quantumForm hD n a = 0 ↔ D.form a n = 0 := by
    rw [← Int.cast_inj (α := ℚ), cast_quantumForm_apply, Int.cast_zero]
  have h₂ : D.normal n hn a = 0 ↔ D.sublattice.toAddSubgroup.rayIndex n * D.form a n = 0 := by
    rw [← Int.cast_inj (α := ℚ), cast_normal_apply, Int.cast_zero]
  simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, h₁, h₂]
  by_cases hn0 : n = 0
  · simp [hn0]
  · rw [mul_eq_zero, or_iff_right (D.sublattice.toAddSubgroup.rayIndex_pos hn0).ne']

/-- Over a nontrivial coefficient ring, the quantum wall space of an unfrozen degree `n` and
an integral normal `m` is nonzero exactly when `m` is nonzero with the kernel of the normalized
normal `{-, κ(n) n}` of the skew datum. -/
theorem wallSubmodule_quantumForm_ne_bot_iff {R : Type*} [CommRing R] [Nontrivial R] (q : Rˣ)
    {n : N} (hn : n ∈ D.unfrozen) (m : N →+ ℤ) :
    QuantumMonoidAlgebra.wallSubmodule q (D.quantumForm hD) n m ≠ ⊥ ↔
      m ≠ 0 ∧ m.ker = (D.normal n hn).toAddMonoidHom.ker := by
  rw [QuantumMonoidAlgebra.wallSubmodule_ne_bot_iff, D.ker_quantumForm hD hn]

end Mei.SkewLatticeDatum
