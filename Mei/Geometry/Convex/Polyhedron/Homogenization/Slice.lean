/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Homogenization
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Basic

/-!
# Recovering a closed cone from its height-one slice

A closed cone in nonnegative heights that meets height one is the actual
homogenization of that slice. Closedness retains the height-zero directions;
nonemptiness of the slice supplies the positive-height approximants.
-/

public section

open Set Filter
open scoped Topology

namespace PointedCone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A closed cone in nonnegative heights, meeting height one, is determined by
its height-one slice, including all its height-zero directions. -/
theorem homogenization_slice_one (C : PointedCone ℝ (V × ℝ))
    (hclosed : IsClosed (C : Set (V × ℝ))) (hheight : ∀ z ∈ C, 0 ≤ z.2)
    (hne : {x : V | (x, (1 : ℝ)) ∈ C}.Nonempty) :
    Set.homogenization {x : V | (x, (1 : ℝ)) ∈ C} = C := by
  let P := {x : V | (x, (1 : ℝ)) ∈ C}
  have hpos {x : V} {t : ℝ} (ht : 0 < t) (hz : (x, t) ∈ C) :
      (x, t) ∈ Set.homogenization P := by
    have hbase : (t⁻¹ • x, (1 : ℝ)) ∈ C := by
      have hm := C.smul_mem (inv_nonneg.mpr ht.le) hz
      simpa [ht.ne'] using hm
    have hm := (Set.homogenization P).smul_mem ht.le
      (Set.mem_homogenization_one hbase)
    convert hm using 1; simp [ht.ne']
  apply le_antisymm
  · exact (Set.homogenization_le_iff hclosed).mpr fun x hx => hx
  · rintro ⟨x, t⟩ hz
    rcases (hheight _ hz).eq_or_lt with rfl | ht
    · obtain ⟨p, hp⟩ := hne
      have hlim : Tendsto (fun ε : ℝ => (x + ε • p, ε)) (𝓝[>] 0) (𝓝 (x, (0 : ℝ))) := by
        have hc : Continuous (fun ε : ℝ => (x + ε • p, ε)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_id
        simpa only [zero_smul, add_zero] using
          (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      apply (Set.isClosed_homogenization P).mem_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hm := C.add_mem hz (C.smul_mem (le_of_lt hε) hp)
      apply hpos hε
      simpa using hm
    · exact hpos ht hz

namespace IsFaceOf

/-- Taking height-one slices preserves the extreme-subset property of a cone face. -/
theorem isExtreme_slice_one {C G : PointedCone ℝ (V × ℝ)} (hG : G.IsFaceOf C) :
    IsExtreme ℝ {x : V | (x, (1 : ℝ)) ∈ C} {x : V | (x, (1 : ℝ)) ∈ G} := by
  refine ⟨fun _ hx => hG.le hx, ?_⟩
  rintro x hx y hy z hz ⟨a, b, ha, hb, hab, heq⟩
  apply hG.mem_of_smul_add_smul_mem_left hx hy ha hb
  have hprod : a • (x, (1 : ℝ)) + b • (y, (1 : ℝ)) = (z, (1 : ℝ)) := by
    apply Prod.ext
    · exact heq
    · simpa using hab
  rw [hprod]
  exact hz

end IsFaceOf

end PointedCone
