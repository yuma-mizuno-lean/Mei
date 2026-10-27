/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.CommonRefinement
public import Mei.Geometry.Convex.PolyhedralCochain.NormalForm

/-!
# Injective coefficient maps on polyhedral cochains

An injective linear map of coefficients induces an injective map of polyhedral
cochains. Thus embedding coefficients in a larger module creates no new
relations, even though cochain equality allows arbitrary subdivisions.
No splitting of the coefficient map or field hypothesis is required; in
particular the result applies to inclusions of submodules over arbitrary rings.

The proof uses `exists_common_complex_presentation` to put a cochain on one
finite complex, and
`ofFinsupp_eq_zero_iff_intersectionPairing_eq_zero` to detect it by transverse
tests. Naturality of the intersection pairing reflects each zero test value
through the coefficient embedding. This allows identities and closedness of
kernel-valued obstruction cochains to be checked in an ambient module.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {R E E' : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']

/-- Injective coefficient maps remain injective after imposing the orientation
and subdivision relations of polyhedral cochains. -/
theorem map_injective (f : E →ₗ[R] E') (hf : Function.Injective f) :
    Function.Injective (map (h := h) (k := k) f) := by
  classical
  apply (map f).ker_eq_bot.1
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨C, g, hg⟩ := exists_common_complex_presentation (fun _ : Unit => x)
  obtain ⟨hrep, hcells⟩ := hg ()
  rw [← hrep] at hx ⊢
  rw [map_ofFinsupp] at hx
  apply (ofFinsupp_eq_zero_iff_intersectionPairing_eq_zero C (g ()) hcells
    (by norm_num : (0 : ℝ) < 1)).mpr
  intro p v _ hv
  have htrans : ∀ σ ∈ (Finsupp.mapRange.linearMap f (g ())).support,
      σ.IsTransverse v := fun σ hσ => hv σ (Finsupp.support_mapRange (hf := f.map_zero) hσ)
  have hzero := intersectionPairing_eq_of_ofFinsupp_eq
    (hx.trans (map_zero ofFinsupp).symm) htrans
    (by simp : ∀ σ ∈ (0 : OrientedCell h k →₀ E').support, σ.IsTransverse v)
  have hnat := LinearMap.congr_fun (OrientedCell.intersectionPairing_comp_mapRange f v) (g ())
  simp only [LinearMap.comp_apply] at hnat
  apply hf
  rw [map_zero]
  exact hnat.symm.trans (by simpa only [map_zero] using hzero)

end Mei.PolyhedralCochain
