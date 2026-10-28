/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Basic
public import Mei.Algebra.PositiveDegrees.FiniteAlphabet

/-!
# Tropical pairings from finite alphabet lifts

Let `m : E → M` be a finite family of exponents, with finite alphabet
`P_E ⊆ M × (E → ℤ)` projecting to `M` by the first coordinate. Given positive degree
data on `L`, a projection `π : L → M` and an additive map `τ` sending each letter
`(m α, e_α)` to a nonzero allowed degree `n_α` with `π n_α = m α`, the lift `τ`
together with the identity on characters of `M` is a tropical pairing with identity
cutoff modulus. Both sides use characters of the same tangent lattice `M`: a character
`ν` acts through `ν ∘ pr_M` on the alphabet and through `ν ∘ π` on `L`.

The existing pairing API then supplies the Lie map on positive tangent fields, its
completed group map, and the intertwining of coefficient actions on `R[P_E] → R[P]`
(`TropicalPairing.mapDomainAlgHom_tropicalVertexCoefficientAction_monoid`).
-/

public section

noncomputable section

namespace Mei.TropicalPairing

open PositiveDegrees

variable {R M E L : Type*} [CommRing R] [AddCommGroup M] [Fintype E] [DecidableEq E]
  [AddCommGroup L] {m : E → M} {e : PositiveDegrees L} {τ : M × (E → ℤ) →+ L}
  (hτ : ∀ α, τ (letter m α) ∈ e.monoid) (hτ0 : ∀ α, τ (letter m α) ≠ 0)
  {π : L →+ M} (hπ : ∀ α, π (τ (letter m α)) = m α) (U : Submodule R (M →+ R))

/-- The tropical pairing of a finite alphabet lift: the lift `τ` of the letters to nonzero
allowed degrees over the same exponents, with identity cutoff modulus, acting as the
identity on characters of the common tangent lattice. -/
def finiteAlphabetLift :
    TropicalPairing (d := finiteAlphabet m) (e := e) (ρ := AddMonoidHom.fst M (E → ℤ))
      (ρ' := π) U :=
  ofDegreeMap (PositiveDegrees.finiteAlphabetLift m hτ hτ0)
    (fun _ hx => by
      rw [PositiveDegrees.finiteAlphabetLift_apply]
      exact eq_fst_of_eq_sum m (σ := π.comp τ) hπ
        ((mem_finiteAlphabet_monoid m).mp hx).2) U

@[simp]
theorem finiteAlphabetLift_degreeMap :
    (finiteAlphabetLift hτ hτ0 hπ U).degreeMap = PositiveDegrees.finiteAlphabetLift m hτ hτ0 := by
  unfold finiteAlphabetLift
  simp

@[simp]
theorem finiteAlphabetLift_characterMap (ν : U) :
    (finiteAlphabetLift hτ hτ0 hπ U).characterMap ν = ν.val := by
  unfold finiteAlphabetLift
  simp

end Mei.TropicalPairing
