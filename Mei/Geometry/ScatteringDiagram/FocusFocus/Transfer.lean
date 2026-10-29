/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Binomial

/-!
# Enumerating focus-focus slab decorations

The homogeneous transfers of an incoming monomial through the slab
`t(1+w)` are indexed exactly by the surviving binomial terms `0 ≤ j ≤ d`.
The enumeration retains both normal and tangential exponents and discards
zero decorations over arbitrary commutative coefficient rings. In the Laurent
chamber, its decorations are `c t^d binom(d,j) y^(-d) w^(b+j)`. In the
focus-focus chamber presentation `x₂y₂=t`, the factor `t^d y₂^(-d)` is
the image of `x₂^d`.

In the upper description the incoming tangential exponent is `b+d` and the
slab parameter is `t(1+w⁻¹)`. The term numbered `d-j` there is the same entire
homogeneous decoration as term `j` below. This supplies the coefficient identity
at a branch whose crossing height passes through zero; it does not classify
geometric histories or construct a global theta section.

We use `NodeAlgebra.exponentCorrespondence`, its binomial transfers and
Mathlib's `Nat.choose_symm`. The slab descriptions follow Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra

variable {R : Type*} [CommRing R] (t c : R) (d : ℕ) (b : ℤ)

/-- The surviving binomial terms enumerate exactly all nonzero homogeneous
transfers through the focus-focus slab. The empty enumeration is allowed. -/
def slabTransferEquiv :
    {j : Fin (d + 1) // c * t ^ d * (d.choose j.val : R) ≠ 0} ≃
      {q : ℤ × ℤ //
        (exponentCorrespondence (single 0 t + single 1 t)).transfer
          ⟨((d : ℤ), b), by simp⟩ q
          ⟨single (d, b) c, single_mem_grade _ _⟩ ≠ 0} :=
  Equiv.ofBijective
    (fun j => ⟨(-(d : ℤ), b + j.val.val),
      (exponentCorrespondence_transfer_ne_zero_iff t c d b 1 (by decide) _).mpr
        ⟨j.val.val, Nat.le_of_lt_succ j.val.isLt, by simp, j.property⟩⟩)
    ⟨by
      intro i j hij
      apply Subtype.ext
      apply Fin.ext
      have he := congrArg (fun q => q.val.2) hij
      exact_mod_cast (add_left_cancel he), by
      rintro ⟨q, hq⟩
      obtain ⟨j, hj, he, hc⟩ :=
        (exponentCorrespondence_transfer_ne_zero_iff t c d b 1 (by decide) q).mp hq
      refine ⟨⟨⟨j, Nat.lt_succ_of_le hj⟩, hc⟩, ?_⟩
      apply Subtype.ext
      simpa using he.symm⟩

/-- The outgoing exponent of a surviving branch is `(-d,b+j)`. -/
@[simp]
theorem slabTransferEquiv_apply
    (j : {j : Fin (d + 1) // c * t ^ d * (d.choose j.val : R) ≠ 0}) :
    (slabTransferEquiv t c d b j).val = (-(d : ℤ), b + j.val.val) := (rfl)

/-- Recover the binomial index directly from the outgoing tangential exponent. -/
@[simp]
theorem slabTransferEquiv_symm_apply_val
    (q : {q : ℤ × ℤ //
      (exponentCorrespondence (single 0 t + single 1 t)).transfer
        ⟨((d : ℤ), b), by simp⟩ q
        ⟨single (d, b) c, single_mem_grade _ _⟩ ≠ 0}) :
    ((slabTransferEquiv t c d b).symm q).val.val = (q.val.2 - b).toNat := by
  have he := congrArg (fun q => q.val.2)
    ((slabTransferEquiv t c d b).apply_symm_apply q)
  rw [slabTransferEquiv_apply] at he
  have hi : (((slabTransferEquiv t c d b).symm q).val.val : ℤ) = q.val.2 - b := by
    dsimp at he
    omega
  rw [← hi, Int.toNat_natCast]

/-- The index recovered from a nonzero transfer reconstructs its outgoing degree. -/
theorem slabTransferEquiv_symm_degree
    (q : {q : ℤ × ℤ //
      (exponentCorrespondence (single 0 t + single 1 t)).transfer
        ⟨((d : ℤ), b), by simp⟩ q
        ⟨single (d, b) c, single_mem_grade _ _⟩ ≠ 0}) :
    (-(d : ℤ), b + ((slabTransferEquiv t c d b).symm q).val.val) = q.val := by
  simpa only [slabTransferEquiv_apply] using
    congrArg Subtype.val ((slabTransferEquiv t c d b).apply_symm_apply q)

/-- Upper and lower descriptions agree at every outgoing homogeneous degree,
including degrees outside the binomial range. -/
theorem slab_transfer_eq_upper (q : ℤ × ℤ) :
    ((exponentCorrespondence (single 0 t + single 1 t)).transfer
      ⟨((d : ℤ), b), by simp⟩ q
      ⟨single (d, b) c, single_mem_grade _ _⟩ : R[ℤ × ℤ]) =
    ((exponentCorrespondence (single 0 t + single (-1) t)).transfer
      ⟨((d : ℤ), b + d), by simp⟩ q
      ⟨single (d, b + d) c, single_mem_grade _ _⟩ : R[ℤ × ℤ]) := by
  have he :
      exponentRightMap (single 0 t + single 1 t)
        (exponentIncomingLift (single 0 t + single 1 t) 0
          ⟨((d : ℤ), b), by simp⟩ ⟨single (d, b) c, single_mem_grade _ _⟩) =
      exponentRightMap (single 0 t + single (-1) t)
        (exponentIncomingLift (single 0 t + single (-1) t) 0
          ⟨((d : ℤ), b + d), by simp⟩ ⟨single (d, b + d) c, single_mem_grade _ _⟩) := by
    rw [exponentRightMap_exponentIncomingLift_binomial,
      exponentRightMap_exponentIncomingLift_binomial,
      ← Finset.sum_range_reflect (fun j =>
        single (-(d : ℤ), b + (d : ℤ) + j • (-1))
          (c * t ^ d * (d.choose j : R))) (d + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hi : d + 1 - 1 - j = d - j := by omega
    have hb : b + (d : ℤ) + (d - j) • (-1 : ℤ) = b + j • (1 : ℤ) := by
      simp only [nsmul_eq_mul, mul_neg_one, mul_one]
      omega
    rw [hi, hb, Nat.choose_symm hjd]
  simpa only [GradedCorrespondence.transfer_apply, exponentCorrespondence_right,
    exponentCorrespondence_liftLeft, AlgHom.toLinearMap_apply] using
    congrArg (fun x => (DirectSum.decompose (grade R) x q : R[ℤ × ℤ])) he

end Mei.FocusFocus
