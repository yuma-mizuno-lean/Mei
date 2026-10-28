/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Lie
public import Mei.Geometry.ScatteringDiagram.WallSpace.Basic

/-!
# Quantum directed wall spaces

The quantum wall space of degree `n` is the whole monomial line when its integral
normal is nonzero and rationally proportional to `β(n,-)`, and zero otherwise.
We express proportionality by equality of kernels of integer characters; this is
equivalent to equality of nonzero integer multiples. Eligibility depends on the
integral alternating form, even when the quantum parameter specializes to one
or to a root of unity.

The contracted-normal identity proves the directed bracket law. When the two
spatial degrees pair to zero, their quantum commutator vanishes; otherwise the
contracted normal has the kernel of `β(n+n',-)`. Restriction to the strictly
positive quantum Lie algebra supplies the wall spaces used for completed labels.

We use `QuantumMonoidAlgebra.lie_monomial`, `supportedLieSubalgebra`, and
`AddMonoidHom.exists_ne_zero_zsmul_eq_of_ker_eq`. The quantum wall convention
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Example 2.1(iii).
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- The quantum monomial line with an eligible integral normal. Zero normals and radical
degrees carry zero wall space, independently of the value of the quantum parameter. -/
def wallSubmodule (n : Γ) (m : Γ →+ ℤ) : Submodule R (QuantumMonoidAlgebra q β) := by
  classical
  exact if m ≠ 0 ∧ m.ker = (β n).toAddMonoidHom.ker then grade q β n else ⊥

/-- Eligible quantum wall spaces are the full homogeneous monomial lines. -/
@[simp]
theorem wallSubmodule_eq_grade {n : Γ} {m : Γ →+ ℤ}
    (hm : m ≠ 0) (hker : m.ker = (β n).toAddMonoidHom.ker) :
    wallSubmodule q β n m = grade q β n := by
  simp [wallSubmodule, hm, hker]

/-- Membership records homogeneous membership and the integral eligibility condition,
unless the element is zero. -/
@[simp]
theorem mem_wallSubmodule_iff (n : Γ) (m : Γ →+ ℤ) (x : QuantumMonoidAlgebra q β) :
    x ∈ wallSubmodule q β n m ↔
      x = 0 ∨ m ≠ 0 ∧ m.ker = (β n).toAddMonoidHom.ker ∧ x ∈ grade q β n := by
  by_cases h : m ≠ 0 ∧ m.ker = (β n).toAddMonoidHom.ker
  · rw [wallSubmodule_eq_grade q β h.1 h.2]
    constructor
    · exact fun hx => Or.inr ⟨h.1, h.2, hx⟩
    · rintro (rfl | ⟨_, _, hx⟩)
      · exact Submodule.zero_mem _
      · exact hx
  · simp only [wallSubmodule, ite_eq_right h, Submodule.mem_bot]
    tauto

/-- The zero normal has no quantum wall elements. -/
@[simp]
theorem wallSubmodule_zero_normal (n : Γ) : wallSubmodule q β n 0 = ⊥ := by
  simp [wallSubmodule]

/-- Radical degrees have no eligible quantum wall normals, even if their monomials
are nonzero central elements. -/
@[simp]
theorem wallSubmodule_eq_bot_of_radical (n : Γ) (h : β n = 0) (m : Γ →+ ℤ) :
    wallSubmodule q β n m = ⊥ := by
  have hk : (β n).toAddMonoidHom.ker = ⊤ := by
    apply AddMonoidHom.ker_eq_top_iff.mpr
    ext v
    simp [h]
  by_cases hm : m = 0
  · simp [hm]
  · have hmker : m.ker ≠ ⊤ := fun he => hm (AddMonoidHom.ker_eq_top_iff.mp he)
    simp [wallSubmodule, hk, hmker]

private theorem contracted_normal_ker {n n' : Γ} {m m' : Γ →+ ℤ}
    (hβ : β.IsAlt) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hk : m.ker = (β n).toAddMonoidHom.ker)
    (hk' : m'.ker = (β n').toAddMonoidHom.ker) (hn : β n n' ≠ 0) :
    (wallBracketNormal (AddMonoidHom.id Γ) n n' m m').ker =
      (β (n + n')).toAddMonoidHom.ker := by
  obtain ⟨a, b, ha, hb, hab⟩ := m.exists_ne_zero_zsmul_eq_of_ker_eq _ hm hk
  obtain ⟨c, d, hc, hd, hcd⟩ := m'.exists_ne_zero_zsmul_eq_of_ker_eq _ hm' hk'
  have habv (v : Γ) : a * m v = b * β n v := DFunLike.congr_fun hab v
  have hcdv (v : Γ) : c * m' v = d * β n' v := DFunLike.congr_fun hcd v
  have hs (v : Γ) :
      (a * c) * wallBracketNormal (AddMonoidHom.id Γ) n n' m m' v =
        (b * d * β n n') * β (n + n') v := by
    simp only [wallBracketNormal_apply, AddMonoidHom.id_apply, map_add, LinearMap.add_apply]
    calc
      a * c * (m n' * m' v - m' n * m v) =
          (a * m n') * (c * m' v) - (c * m' n) * (a * m v) := by ring
      _ = (b * β n n') * (d * β n' v) - (d * (-β n n')) * (b * β n v) := by
        rw [habv, hcdv, hcdv, habv, ← hβ.neg_eq n n']
      _ = b * d * β n n' * (β n v + β n' v) := by ring
  ext v
  simp only [AddMonoidHom.mem_ker]
  have he := hs v
  have hac : a * c ≠ 0 := mul_ne_zero ha hc
  have hbd : b * d * β n n' ≠ 0 := mul_ne_zero (mul_ne_zero hb hd) hn
  constructor
  · intro hv
    rw [hv, mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hbd
  · intro hv
    have hv' : β (n + n') v = 0 := hv
    rw [hv', mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hac

/-- Quantum monomial lines satisfy all homogeneous directed-wall laws. -/
def ambientWallSpaces (hβ : β.IsAlt) :
    DirectedWallSpaces (AddMonoidHom.id Γ) (grade q β) where
  wall := wallSubmodule q β
  wall_le_piece n m := by
    unfold wallSubmodule
    split_ifs
    · exact le_rfl
    · exact bot_le
  zero_normal n := by simp [wallSubmodule]
  nontangent n m hm := by
    have h : m.ker ≠ (β n).toAddMonoidHom.ker := by
      intro hk
      have hn : n ∈ (β n).toAddMonoidHom.ker := hβ.self_eq_zero n
      exact hm (AddMonoidHom.mem_ker.mp (hk ▸ hn))
    simp [wallSubmodule, h]
  rescale n m c hc := by
    classical
    have hk : (c • m).ker = m.ker := by
      ext v
      simp [AddMonoidHom.mem_ker, hc]
    have hz : c • m = 0 ↔ m = 0 := by
      constructor
      · intro h
        ext v
        have hv := DFunLike.congr_fun h v
        simpa [hc] using hv
      · rintro rfl; simp
    unfold wallSubmodule
    apply ite_cond_congr
    apply propext
    exact and_congr (not_congr hz) (by rw [hk])
  bracket_mem := by
    intro n n' m m' x y hx hy
    rcases (mem_wallSubmodule_iff q β n m x).mp hx with rfl | ⟨hm, hk, hx⟩
    · simpa only [zero_lie] using (wallSubmodule q β _ _).zero_mem
    rcases (mem_wallSubmodule_iff q β n' m' y).mp hy with rfl | ⟨hm', hk', hy⟩
    · simpa only [lie_zero] using (wallSubmodule q β _ _).zero_mem
    obtain ⟨r, rfl⟩ := (mem_grade_iff q β n x).mp hx
    obtain ⟨s, rfl⟩ := (mem_grade_iff q β n' y).mp hy
    by_cases hn : β n n' = 0
    · simp [lie_smul, smul_lie, lie_monomial q β hβ, hn]
    · have hker := contracted_normal_ker β hβ hm hm' hk hk' hn
      have hnormal : wallBracketNormal (AddMonoidHom.id Γ) n n' m m' ≠ 0 := by
        intro hz
        have ht : n ∈ (β (n + n')).toAddMonoidHom.ker := by
          rw [← hker, hz]; simp
        have he : β n' n = 0 := by simpa [hβ.self_eq_zero] using ht
        exact hn (neg_eq_zero.mp ((hβ.neg_eq n n').trans he))
      rw [wallSubmodule_eq_grade q β hnormal hker]
      exact SetLike.GradedBracket.bracket_mem
        ((grade q β n).smul_mem r ((mem_grade_iff q β n _).mpr ⟨1, one_smul _ _⟩))
        ((grade q β n').smul_mem s ((mem_grade_iff q β n' _).mpr ⟨1, one_smul _ _⟩))

/-- The ambient quantum wall space has the stated eligibility and monomial formula. -/
@[simp]
theorem ambientWallSpaces_wall (hβ : β.IsAlt) (n : Γ) (m : Γ →+ ℤ) :
    (ambientWallSpaces q β hβ).wall n m = wallSubmodule q β n m := (rfl)

variable (d : PositiveDegrees Γ)

/-- Restrict the quantum wall spaces to the strictly positive quantum Lie algebra. -/
def wallSpaces (hβ : β.IsAlt) :
    DirectedWallSpaces (AddMonoidHom.id Γ) (positiveLieGrading q β d) where
  wall n m := (wallSubmodule q β n m).comap (positiveLieAlgebra q β d).incl.toLinearMap
  wall_le_piece n m := by
    rw [positiveLieGrading_def]
    exact Submodule.comap_mono ((ambientWallSpaces q β hβ).wall_le_piece n m)
  zero_normal n := by
    rw [← ambientWallSpaces_wall q β hβ, (ambientWallSpaces q β hβ).zero_normal]
    exact LinearMap.ker_eq_bot_of_injective Subtype.val_injective
  nontangent n m hm := by
    rw [← ambientWallSpaces_wall q β hβ, (ambientWallSpaces q β hβ).nontangent n m hm]
    exact LinearMap.ker_eq_bot_of_injective Subtype.val_injective
  rescale n m c hc := by
    rw [← ambientWallSpaces_wall q β hβ, (ambientWallSpaces q β hβ).rescale n m c hc,
      ambientWallSpaces_wall]
  bracket_mem hx hy := (ambientWallSpaces q β hβ).bracket_mem hx hy

/-- Positive quantum wall spaces are inverse images under the ambient inclusion. -/
@[simp]
theorem wallSpaces_wall (hβ : β.IsAlt) (n : Γ) (m : Γ →+ ℤ) :
    (wallSpaces q β d hβ).wall n m =
      (wallSubmodule q β n m).comap (positiveLieAlgebra q β d).incl.toLinearMap := (rfl)

/-- In a nonzero allowed degree the positive restriction retains the full quantum
wall line; it discards no eligible coefficient. -/
theorem map_wallSpaces_wall (hβ : β.IsAlt) {n : Γ}
    (hn : n ∈ d.monoid) (hne : n ≠ 0) (m : Γ →+ ℤ) :
    ((wallSpaces q β d hβ).wall n m).map (positiveLieAlgebra q β d).incl.toLinearMap =
      wallSubmodule q β n m := by
  rw [wallSpaces_wall, Submodule.map_comap_eq]
  apply inf_eq_right.mpr
  intro x hx
  exact ⟨⟨x, grade_le_positiveLieAlgebra q β d hn hne
    ((ambientWallSpaces q β hβ).wall_le_piece n m hx)⟩, rfl⟩

end Mei.QuantumMonoidAlgebra
