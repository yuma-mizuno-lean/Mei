/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.GraphPerturbation
public import Mei.Geometry.Convex.Polyhedron.SegmentSubdivision
public import Mei.Topology.ContinuousMap.Subdivision

/-!
# Admissible filling grids with fixed boundary

A continuous square with four affine admissible boundary edges has an admissible
grid subordinate to any open cover of its image. Every boundary vertex stays on
the original parameterized boundary; only interior vertices are perturbed. The
original patch and the convex hull of its perturbed corners remain in one cover
member. Thus local relations can be assembled without changing the filled loop.

The construction combines `ContinuousMap.exists_grid_subdivision_convexHull`,
avoiding the finitely many boundary crossing times, with
`Convex.exists_admissible_graph_perturbation`. Boundary edges are subsegments of
the given edges, using `WallComplement.AdmissibleSegment.subsegment`. Neither
the square nor its boundary is required to be embedded or nondegenerate.
-/

public section

noncomputable section

open Set
open scoped unitInterval

namespace Mei.Convex

variable {V ι : Type*} {κ : Sort*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι]

/-- Subdivide a square with affine admissible sides under an open cover, keeping
all boundary vertices fixed. The mesh avoids boundary wall crossings, so each
boundary edge is an admissible subsegment of the original side. Every original
patch and the convex hull of its new corners lie in a common cover member.
Interior vertices can be perturbed by less than any prescribed positive tolerance. -/
theorem exists_admissible_filling_grid_fixed_boundary
    (W : ι → Set V) (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V)
    (x : Fin 2 × Fin 2 → WallComplement W)
    (e₁ : ∀ b : Fin 2, x (0, b) ⟶ x (1, b))
    (e₂ : ∀ a : Fin 2, x (a, 0) ⟶ x (a, 1))
    (f : C(↥unitInterval × ↥unitInterval, V))
    (hf₁ : ∀ (b : Fin 2) (s : unitInterval),
      f (s, if b = 0 then 0 else 1) =
        AffineMap.lineMap (x (0, b)).val (x (1, b)).val (s : ℝ))
    (hf₂ : ∀ (a : Fin 2) (s : unitInterval),
      f (if a = 0 then 0 else 1, s) =
        AffineMap.lineMap (x (a, 0)).val (x (a, 1)).val (s : ℝ))
    (U : κ → Set V) (hU : ∀ j, IsOpen (U j)) (hcover : ∀ z, ∃ j, f z ∈ U j)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (t : ℕ → unitInterval), 0 < n ∧ t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
      ∃ v : Fin (n + 1) × Fin (n + 1) → WallComplement W,
        (∀ c, c.1 = 0 ∨ c.1 = Fin.last n ∨ c.2 = 0 ∨ c.2 = Fin.last n →
          (v c).val = f (t c.1, t c.2)) ∧
        (∀ c, dist (v c).val (f (t c.1, t c.2)) < η) ∧
      ∃ (_ : ∀ (a : Fin n) (b : Fin (n + 1)),
          v (a.castSucc, b) ⟶ v (a.succ, b))
        (_ : ∀ (a : Fin (n + 1)) (b : Fin n),
          v (a, b.castSucc) ⟶ v (a, b.succ)),
      ∀ a b : Fin n, ∃ j,
        MapsTo f (Icc (t a) (t (a + 1)) ×ˢ Icc (t b) (t (b + 1))) (U j) ∧
        convexHull ℝ (range (fun c : Fin 2 × Fin 2 =>
          (v (⟨a.val + c.1.val, by omega⟩, ⟨b.val + c.2.val, by omega⟩)).val)) ⊆ U j := by
  classical
  -- Boundary crossings give a finite set of forbidden mesh times.
  let S := (⋃ b : Fin 2,
      Prod.snd '' WallComplement.crossings (x (0, b)) (x (1, b))) ∪
    ⋃ a : Fin 2, Prod.snd '' WallComplement.crossings (x (a, 0)) (x (a, 1))
  have hS : S.Countable :=
    ((finite_iUnion fun b => (e₁ b).down.finite_crossings.image Prod.snd).union
      (finite_iUnion fun a => (e₂ a).down.finite_crossings.image Prod.snd)).countable
  have hend (z : ℝ) (hz : z = 0 ∨ z = 1) : z ∉ S := by
    have he (a b : WallComplement W) : z ∉ Prod.snd '' WallComplement.crossings a b := by
      rintro ⟨⟨j, s⟩, hs, rfl⟩
      have hs' := (WallComplement.mem_crossings a b j s).mp hs
      rcases hz with rfl | rfl
      · exact a.notMem j (by simpa only [AffineMap.lineMap_apply_zero] using hs'.2)
      · exact b.notMem j (by simpa only [AffineMap.lineMap_apply_one] using hs'.2)
    simpa only [S, mem_union, mem_iUnion, not_or, not_exists] using
      And.intro (fun b => he (x (0, b)) (x (1, b)))
        (fun a => he (x (a, 0)) (x (a, 1)))
  obtain ⟨n, t, hn, ht0, htmono, ht1, htS, ε, hε, hgrid⟩ :=
    f.exists_grid_subdivision_convexHull U hU hcover S hS
      (hend 0 (Or.inl rfl)) (hend 1 (Or.inr rfl))
  -- Choose the mesh before fixing its boundary vertices.
  let z : Fin (n + 1) × Fin (n + 1) → V := fun c => f (t c.1, t c.2)
  let B : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter fun c =>
      c.1 = 0 ∨ c.1 = Fin.last n ∨ c.2 = 0 ∨ c.2 = Fin.last n
  have hB (c) : c ∈ B ↔
      c.1 = 0 ∨ c.1 = Fin.last n ∨ c.2 = 0 ∨ c.2 = Fin.last n := by simp [B]
  have hside₁ (b : Fin 2) (m : ℕ) (j : ι) :
      f (t m, if b = 0 then 0 else 1) ∉ W j := by
    rw [hf₁]
    intro hj
    exact htS m (Or.inl (mem_iUnion.mpr ⟨b, ⟨(j, t m),
      (WallComplement.mem_crossings _ _ _ _).mpr ⟨(t m).property, hj⟩, rfl⟩⟩))
  have hside₂ (a : Fin 2) (m : ℕ) (j : ι) :
      f (if a = 0 then 0 else 1, t m) ∉ W j := by
    rw [hf₂]
    intro hj
    exact htS m (Or.inr (mem_iUnion.mpr ⟨a, ⟨(j, t m),
      (WallComplement.mem_crossings _ _ _ _).mpr ⟨(t m).property, hj⟩, rfl⟩⟩))
  have hfixed (c) (hc : c ∈ B) (j : ι) : z c ∉ W j := by
    rcases (hB c).mp hc with hc | hc | hc | hc
    · simpa only [z, hc, Fin.val_zero, ht0, ite_true] using hside₂ 0 c.2 j
    · simpa only [z, hc, Fin.val_last, ht1, show (1 : Fin 2) ≠ 0 by decide,
        ite_false] using hside₂ 1 c.2 j
    · simpa only [z, hc, Fin.val_zero, ht0, ite_true] using hside₁ 0 c.1 j
    · simpa only [z, hc, Fin.val_last, ht1, show (1 : Fin 2) ≠ 0 by decide,
        ite_false] using hside₁ 1 c.1 j
  let edge := fun c d : Fin (n + 1) × Fin (n + 1) =>
    (d.1.val = c.1.val + 1 ∧ d.2 = c.2) ∨
      (d.1 = c.1 ∧ d.2.val = c.2.val + 1)
  -- Edges between fixed vertices lie on a side, even for a one-cell grid.
  have hedge (c) (hc : c ∈ B) (d) (hd : d ∈ B) (he : edge c d) :
      (z c, z d) ∈ admissiblePairs W := by
    let p : WallComplement W := ⟨z c, hfixed c hc⟩
    let q : WallComplement W := ⟨z d, hfixed d hd⟩
    apply (mem_admissiblePairs_iff p q).mpr
    have hc' := (hB c).mp hc
    have hd' := (hB d).mp hd
    rcases he with ⟨hstep, hrow⟩ | ⟨hcol, hstep⟩
    · have hb : c.2 = 0 ∨ c.2 = Fin.last n := by
        apply or_iff_not_imp_left.mpr
        intro hne
        apply Fin.ext
        have hne' : c.2.val ≠ 0 := fun hz => hne (Fin.ext hz)
        simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last] at hc' hd' ⊢
        have hd2 : d.2.val = c.2.val := congrArg Fin.val hrow
        omega
      rcases hb with hb | hb
      · exact (e₁ 0).down.subsegment (t c.1).property (t d.1).property
          (by simp [p, z, hb, ht0, ← hf₁])
          (by simp [q, z, hrow, hb, ht0, ← hf₁])
      · exact (e₁ 1).down.subsegment (t c.1).property (t d.1).property
          (by simp [p, z, hb, ht1, ← hf₁])
          (by simp [q, z, hrow, hb, ht1, ← hf₁])
    · have ha : c.1 = 0 ∨ c.1 = Fin.last n := by
        apply or_iff_not_imp_left.mpr
        intro hne
        apply Fin.ext
        have hne' : c.1.val ≠ 0 := fun hz => hne (Fin.ext hz)
        simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last] at hc' hd' ⊢
        have hd1 : d.1.val = c.1.val := congrArg Fin.val hcol
        omega
      rcases ha with ha | ha
      · exact (e₂ 0).down.subsegment (t c.2).property (t d.2).property
          (by simp [p, z, ha, ht0, ← hf₂])
          (by simp [q, z, hcol, ha, ht0, ← hf₂])
      · exact (e₂ 1).down.subsegment (t c.2).property (t d.2).property
          (by simp [p, z, ha, ht1, ← hf₂])
          (by simp [q, z, hcol, ha, ht1, ← hf₂])
  -- Perturb only the interior; the cover margin retains all patch containments.
  obtain ⟨w, hwfix, hwnear, hwallowed, hwedge⟩ :=
    exists_admissible_graph_perturbation W hpoly hdim z edge B hfixed hedge
      (fun _ => min ε η) (fun _ => lt_min hε hη)
  let v : Fin (n + 1) × Fin (n + 1) → WallComplement W := fun c => ⟨w c, hwallowed c⟩
  have hedge' (c d) (hcd : edge c d) : Nonempty (v c ⟶ v d) :=
    ⟨PLift.up ((mem_admissiblePairs_iff (v c) (v d)).mp (hwedge c d hcd))⟩
  refine ⟨n, t, hn, ht0, htmono, ht1, v,
    fun c hc => hwfix c ((hB c).mpr hc),
    fun c => (hwnear c).trans_le (min_le_right _ _),
    fun a b => (hedge' (a.castSucc, b) (a.succ, b) (Or.inl ⟨rfl, rfl⟩)).some,
    fun a b => (hedge' (a, b.castSucc) (a, b.succ) (Or.inr ⟨rfl, rfl⟩)).some,
    fun a b => ?_⟩
  obtain ⟨j, hj, hhull⟩ := hgrid a b
  exact ⟨j, hj, hhull _ (fun c => (hwnear _).trans_le (min_le_left _ _))⟩

end Mei.Convex
