/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Incidence

/-!
# Reductions of the upper focus-focus gluing presentation

Coefficient changes and cutoff reductions on the lower slab transport to
its upper gluing presentation. On actual upper matching pairs, the resulting
map is precisely the pair of canonical chamber reductions. These maps respect
identity and composition, preserve the entire tangential coefficient algebra,
and commute with the equivalence between the two gluing presentations. Thus
the gluing comparison identifies the coefficient towers, rather than just
their individual rings.

We use `upperSlabEquiv`, `truncatedExponentChamberMap_upper` and
`truncatedSlabMap`, together with Mathlib's composition of ring homomorphisms.
The upper coordinate and gluing conventions follow
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open Mei.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable {K K' K'' : Type*} [CommRing K] [CommRing K'] [CommRing K'']
  {k l m : ℕ} (φ : K →+* K') (hl : l ≤ k)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "S'" => AdjoinRoot (Polynomial.X ^ (l + 1) : Polynomial K')
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ'" => AdjoinRoot.root (Polynomial.X ^ (l + 1) : Polynomial K')

/-- Change coefficients and lower the cutoff in the upper gluing presentation.
Transport the lower slab reduction through the two gluing equivalences. -/
def truncatedUpperSlabMap : upperSlabAlgebra τ k →+* upperSlabAlgebra τ' l :=
  (upperSlabEquiv K' l).toRingHom.comp
    ((truncatedSlabMap φ hl).comp (upperSlabEquiv K k).symm.toRingHom)

/-- Upper slab reduction is the pair of the canonical chamber reductions. -/
@[simp]
theorem coe_truncatedUpperSlabMap (z : upperSlabAlgebra τ k) :
    (truncatedUpperSlabMap φ hl z).val =
      (truncatedExponentChamberMap φ hl 1 z.val.1,
        truncatedExponentChamberMap φ hl 0 z.val.2) := by
  simp [truncatedUpperSlabMap, ← truncatedExponentChamberMap_upper]

/-- Changing neither coefficients nor cutoff fixes every upper matching pair. -/
@[simp]
theorem truncatedUpperSlabMap_id :
    truncatedUpperSlabMap (RingHom.id K) (k := k) le_rfl = RingHom.id _ := by
  ext z : 1
  apply Subtype.ext
  apply Prod.ext <;> simp

/-- Upper matching-pair reductions respect composition of coefficient maps
and cutoff transitions. -/
theorem truncatedUpperSlabMap_comp (ψ : K' →+* K'') (hm : m ≤ l) :
    (truncatedUpperSlabMap ψ hm).comp (truncatedUpperSlabMap φ hl) =
      truncatedUpperSlabMap (ψ.comp φ) (hm.trans hl) := by
  ext z : 1
  apply Subtype.ext
  apply Prod.ext <;> simp only [RingHom.comp_apply, coe_truncatedUpperSlabMap]
  · exact RingHom.congr_fun (truncatedExponentChamberMap_comp φ hl 1 ψ hm) z.val.1
  · exact RingHom.congr_fun (truncatedExponentChamberMap_comp φ hl 0 ψ hm) z.val.2

/-- The entire tangential coefficient algebra uses the original scalar
reduction, including the truncated smoothing parameter. -/
@[simp]
theorem truncatedUpperSlabMap_algebraMap (a : S[ℤ]) :
    truncatedUpperSlabMap φ hl (algebraMap S[ℤ] (upperSlabAlgebra τ k) a) =
      algebraMap S'[ℤ] (upperSlabAlgebra τ' l) (truncatedScalarMap φ hl a) := by
  apply Subtype.ext
  apply Prod.ext <;> simp

/-- The upper/lower gluing equivalence is natural under coefficient changes
and cutoff reductions on the actual matching pairs. -/
@[simp]
theorem truncatedUpperSlabMap_upperSlabEquiv (z : slabAlgebra (C τ) (1 + T 1) k) :
    truncatedUpperSlabMap φ hl (upperSlabEquiv K k z) =
      upperSlabEquiv K' l (truncatedSlabMap φ hl z) := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [coe_truncatedUpperSlabMap, coe_upperSlabEquiv, truncatedSlabMap_fst]
    exact truncatedExponentChamberMap_upper K k 1 φ hl z.val.1
  · simp

/-- Returning to the lower gluing presentation also commutes with reduction. -/
@[simp]
theorem upperSlabEquiv_symm_truncatedUpperSlabMap (z : upperSlabAlgebra τ k) :
    (upperSlabEquiv K' l).symm (truncatedUpperSlabMap φ hl z) =
      truncatedSlabMap φ hl ((upperSlabEquiv K k).symm z) := by
  apply (upperSlabEquiv K' l).injective
  simp only [AlgEquiv.apply_symm_apply, ← truncatedUpperSlabMap_upperSlabEquiv]

end Mei.FocusFocus
