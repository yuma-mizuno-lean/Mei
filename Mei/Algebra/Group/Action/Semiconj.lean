/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Scalar multiples of semiconjugate products

In a semigroup whose scalar action commutes with multiplication on both sides,
a semiconjugating factor moves across a product with a common scalar multiple.
-/

public section

namespace SemiconjBy

/-- Move a semiconjugating factor across a scalar multiple and two trailing factors. -/
theorem smul_mul_mul {R A : Type*} [Semigroup A] [SMul R A]
    [SMulCommClass R A A] [IsScalarTower R A A]
    {u v w : A} (h : SemiconjBy u w v) (r : R) (a b : A) :
    r • (u * (w * a * b)) = v * (r • (u * a)) * b := by
  simp only [mul_smul_comm, smul_mul_assoc, ← mul_assoc, h.eq.symm]

end SemiconjBy
