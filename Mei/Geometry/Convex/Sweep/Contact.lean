/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Topology
public import Mei.Analysis.Convex.Intrinsic

/-!
# Persistence of transverse wall contacts

A line meeting the relative interior of a wall transversely still meets that
wall when its base point and the ends of its parameter interval move slightly.
The wall need not be closed, convex, bounded or polyhedral. Its affine span
must be the level hyperplane of the prescribed continuous normal.

Consequently, a limit of wall-avoiding segments can meet that wall transversely
only on its relative boundary. The same argument applies to incoming half-lines
by restricting to a finite interval around the contact.

We use `sweepProjection` to locate the crossing and
`Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior` to keep it in the wall,
the same relative-neighborhood argument used for admissible-segment stability
in `Mei.Geometry.Convex.Polyhedron.Perturbation`.
-/

public section

open Set Filter Topology Mei.Convex

namespace ContinuousLinearMap

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]

/-- A transverse relative-interior contact persists under continuous variation
of the base point and both interval endpoints. -/
theorem eventually_exists_add_smul_mem (f : V →L[ℝ] ℝ) {c : ℝ} {P : Set V}
    (hspan : (affineSpan ℝ P : Set V) = {x | f x = c}) {v : V} (hv : f v ≠ 0)
    {x : X → V} {a b : X → ℝ} {Q : X}
    (hx : ContinuousAt x Q) (ha : ContinuousAt a Q) (hb : ContinuousAt b Q)
    {t : ℝ} (hat : a Q < t) (htb : t < b Q)
    (hcontact : x Q + t • v ∈ intrinsicInterior ℝ P) :
    ∀ᶠ Q' in 𝓝 Q, ∃ s : ℝ, a Q' < s ∧ s < b Q' ∧ x Q' + s • v ∈ P := by
  let τ : X → ℝ := fun Q' => (c - f (x Q')) / f v
  let g : X → V := fun Q' => sweepProjection f c ((f v)⁻¹ • v) (x Q')
  have ht : τ Q = t := (f.toLinearMap.eq_div_of_apply_add_smul_eq hv
    (hspan.subset (subset_affineSpan ℝ P (intrinsicInterior_subset hcontact)))).symm
  have hτ : ContinuousAt τ Q :=
    (continuousAt_const.sub (f.continuous.continuousAt.comp hx)).div_const _
  have hg : ContinuousAt g Q := (sweepProjection f c _).continuous.continuousAt.comp hx
  have hformula (Q' : X) : g Q' = x Q' + τ Q' • v := by
    simp only [g, sweepProjection_apply, smul_smul, τ, div_eq_mul_inv]
  have hgspan : ∀ Q', g Q' ∈ affineSpan ℝ P := by
    intro Q'
    exact hspan.symm.subset (sweepProjection_height f c (by simp [hv]) (x Q'))
  have hlim : Tendsto g (𝓝 Q) (𝓝[affineSpan ℝ P] (x Q + t • v)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hformula, ht] using hg.tendsto,
      Eventually.of_forall hgspan⟩
  filter_upwards [ha.eventually_lt hτ (ht.symm ▸ hat),
    hτ.eventually_lt hb (ht.symm ▸ htb),
    hlim.eventually (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hcontact)]
      with Q' hleft hright hmem
  exact ⟨τ Q', hleft, hright, (hformula Q') ▸ hmem⟩

/-- At a limiting endpoint of a family of avoiding segments, an interior
parameter cannot give a transverse contact in the wall's relative interior. -/
theorem notMem_intrinsicInterior_of_mem_closure_of_avoids (f : V →L[ℝ] ℝ)
    {c : ℝ} {P : Set V}
    (hspan : (affineSpan ℝ P : Set V) = {x | f x = c}) {v : V} (hv : f v ≠ 0)
    {x : X → V} {a b : X → ℝ} {Q : X} {D : Set X}
    (hx : ContinuousAt x Q) (ha : ContinuousAt a Q) (hb : ContinuousAt b Q)
    (havoid : ∀ Q' ∈ D, ∀ s : ℝ, a Q' < s → s < b Q' → x Q' + s • v ∉ P)
    (hQ : Q ∈ closure D) {t : ℝ} (hat : a Q < t) (htb : t < b Q) :
    x Q + t • v ∉ intrinsicInterior ℝ P := by
  intro hcontact
  obtain ⟨Q', hQ'D, s, has, hsb, hmem⟩ :=
    (mem_closure_iff_frequently.mp hQ).and_eventually
      (f.eventually_exists_add_smul_mem hspan hv hx ha hb hat htb hcontact) |>.exists
  exact havoid Q' hQ'D s has hsb hmem

end ContinuousLinearMap
