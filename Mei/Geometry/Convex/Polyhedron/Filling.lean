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

A continuous square with polygonal admissible boundary sides has an admissible
grid subordinate to any open cover of its image. Every boundary vertex stays on
the original parameterized boundary; only interior vertices are perturbed. The
original patch and the convex hull of its perturbed corners remain in one cover
member. Thus local relations can be assembled without changing the filled loop.

The sides are described by a countable set of parameters off which they avoid the
walls and a finite set of breakpoints between which they are admissible segments
(`Mei.Convex.exists_admissible_filling_grid_of_sides`); four affine sides are the case
without breakpoints (`Mei.Convex.exists_admissible_filling_grid_fixed_boundary`).

The construction combines `ContinuousMap.exists_grid_subdivision_convexHull`,
avoiding the boundary wall crossings and passing through the breakpoints, with
`Convex.exists_admissible_graph_perturbation`. For affine sides, boundary edges are
subsegments of the given edges, using `WallComplement.AdmissibleSegment.subsegment`.
Neither the square nor its boundary is required to be embedded or nondegenerate.
-/

public section

noncomputable section

open Set
open scoped unitInterval

namespace Mei.Convex

variable {V ι : Type*} {κ : Sort*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι]

/-- Subdivide a square with polygonal admissible sides under an open cover, keeping all
boundary vertices fixed. Off a countable set `S` of parameters the four sides avoid the walls,
and between two such parameters not separated by a time of the finite set `T`, each side is an
admissible straight segment. The mesh avoids `S` and passes through `T`, so each boundary edge
is such a segment. Every original patch and the convex hull of its new corners lie in a common
cover member. Interior vertices can be perturbed by less than any prescribed positive
tolerance. -/
theorem exists_admissible_filling_grid_of_sides
    (W : ι → Set V) (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V)
    (f : C(↥unitInterval × ↥unitInterval, V))
    (S : Set ℝ) (hS : S.Countable) (h0 : (0 : ℝ) ∉ S) (h1 : (1 : ℝ) ∉ S)
    (hSside : ∀ s r : unitInterval, (r = 0 ∨ r = 1) → (s : ℝ) ∉ S → ∀ j,
      f (s, r) ∉ W j ∧ f (r, s) ∉ W j)
    (T : Finset unitInterval) (hT : ∀ τ ∈ T, (τ : ℝ) ∉ S)
    (hside : ∀ s₁ s₂ r : unitInterval, (r = 0 ∨ r = 1) → s₁ ≤ s₂ → (s₁ : ℝ) ∉ S →
      (s₂ : ℝ) ∉ S → (∀ τ ∈ T, τ ≤ s₁ ∨ s₂ ≤ τ) →
      (f (s₁, r), f (s₂, r)) ∈ admissiblePairs W ∧ (f (r, s₁), f (r, s₂)) ∈ admissiblePairs W)
    (U : κ → Set V) (hU : ∀ j, IsOpen (U j)) (hcover : ∀ z, ∃ j, f z ∈ U j)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (t : ℕ → unitInterval), 0 < n ∧ t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
      (∀ τ ∈ T, ∃ a ≤ n, t a = τ) ∧
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
  obtain ⟨n, t, hn, ht0, htmono, ht1, htS, htT, ε, hε, hgrid⟩ :=
    f.exists_grid_subdivision_convexHull U hU hcover S hS h0 h1 T hT
  -- Choose the mesh before fixing its boundary vertices.
  let z : Fin (n + 1) × Fin (n + 1) → V := fun c => f (t c.1, t c.2)
  let B : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter fun c =>
      c.1 = 0 ∨ c.1 = Fin.last n ∨ c.2 = 0 ∨ c.2 = Fin.last n
  have hB (c) : c ∈ B ↔
      c.1 = 0 ∨ c.1 = Fin.last n ∨ c.2 = 0 ∨ c.2 = Fin.last n := by simp [B]
  have hfixed (c) (hc : c ∈ B) (j : ι) : z c ∉ W j := by
    rcases (hB c).mp hc with hc | hc | hc | hc
    · simpa only [z, hc, Fin.val_zero, ht0] using (hSside _ 0 (Or.inl rfl) (htS _) j).2
    · simpa only [z, hc, Fin.val_last, ht1] using (hSside _ 1 (Or.inr rfl) (htS _) j).2
    · simpa only [z, hc, Fin.val_zero, ht0] using (hSside _ 0 (Or.inl rfl) (htS _) j).1
    · simpa only [z, hc, Fin.val_last, ht1] using (hSside _ 1 (Or.inr rfl) (htS _) j).1
  -- Consecutive mesh times are not separated by a prescribed time.
  have hsep (a : ℕ) : ∀ τ ∈ T, τ ≤ t a ∨ t (a + 1) ≤ τ := by
    intro τ hτ
    obtain ⟨c, -, rfl⟩ := htT τ hτ
    rcases le_or_gt c a with hca | hca
    · exact Or.inl (htmono hca)
    · exact Or.inr (htmono (by omega))
  let edge := fun c d : Fin (n + 1) × Fin (n + 1) =>
    (d.1.val = c.1.val + 1 ∧ d.2 = c.2) ∨
      (d.1 = c.1 ∧ d.2.val = c.2.val + 1)
  -- Edges between fixed vertices lie on a side, even for a one-cell grid.
  have hedge (c) (hc : c ∈ B) (d) (hd : d ∈ B) (he : edge c d) :
      (z c, z d) ∈ admissiblePairs W := by
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
      have hside' := hside (t c.1) (t d.1) (t c.2) (by
          rcases hb with hb | hb
          · exact Or.inl (by simp [hb, ht0])
          · exact Or.inr (by simp [hb, ht1]))
        (htmono (by omega)) (htS _) (htS _) (by simpa only [hstep] using hsep c.1)
      simpa only [z, hrow] using hside'.1
    · have ha : c.1 = 0 ∨ c.1 = Fin.last n := by
        apply or_iff_not_imp_left.mpr
        intro hne
        apply Fin.ext
        have hne' : c.1.val ≠ 0 := fun hz => hne (Fin.ext hz)
        simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last] at hc' hd' ⊢
        have hd1 : d.1.val = c.1.val := congrArg Fin.val hcol
        omega
      have hside' := hside (t c.2) (t d.2) (t c.1) (by
          rcases ha with ha | ha
          · exact Or.inl (by simp [ha, ht0])
          · exact Or.inr (by simp [ha, ht1]))
        (htmono (by omega)) (htS _) (htS _) (by simpa only [hstep] using hsep c.2)
      simpa only [z, hcol] using hside'.2
  -- Perturb only the interior; the cover margin retains all patch containments.
  obtain ⟨w, hwfix, hwnear, hwallowed, hwedge⟩ :=
    exists_admissible_graph_perturbation W hpoly hdim z edge B hfixed hedge
      (fun _ => min ε η) (fun _ => lt_min hε hη)
  let v : Fin (n + 1) × Fin (n + 1) → WallComplement W := fun c => ⟨w c, hwallowed c⟩
  have hedge' (c d) (hcd : edge c d) : Nonempty (v c ⟶ v d) :=
    ⟨PLift.up ((mem_admissiblePairs_iff (v c) (v d)).mp (hwedge c d hcd))⟩
  refine ⟨n, t, hn, ht0, htmono, ht1, htT, v,
    fun c hc => hwfix c ((hB c).mpr hc),
    fun c => (hwnear c).trans_le (min_le_right _ _),
    fun a b => (hedge' (a.castSucc, b) (a.succ, b) (Or.inl ⟨rfl, rfl⟩)).some,
    fun a b => (hedge' (a, b.castSucc) (a, b.succ) (Or.inr ⟨rfl, rfl⟩)).some,
    fun a b => ?_⟩
  obtain ⟨j, hj, hhull⟩ := hgrid a b
  exact ⟨j, hj, hhull _ (fun c => (hwnear _).trans_le (min_le_left _ _))⟩

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
  -- Each side is one affine segment, indexed by the corresponding `Fin 2` coordinate.
  have hrow (s r : unitInterval) (hr : r = 0 ∨ r = 1) :
      ∃ b : Fin 2, f (s, r) = AffineMap.lineMap (x (0, b)).val (x (1, b)).val (s : ℝ) := by
    rcases hr with rfl | rfl
    · exact ⟨0, by simpa using hf₁ 0 s⟩
    · exact ⟨1, by simpa using hf₁ 1 s⟩
  have hcol (s r : unitInterval) (hr : r = 0 ∨ r = 1) :
      ∃ a : Fin 2, f (r, s) = AffineMap.lineMap (x (a, 0)).val (x (a, 1)).val (s : ℝ) := by
    rcases hr with rfl | rfl
    · exact ⟨0, by simpa using hf₂ 0 s⟩
    · exact ⟨1, by simpa using hf₂ 1 s⟩
  have hSside (s r : unitInterval) (hr : r = 0 ∨ r = 1) (hs : (s : ℝ) ∉ S) (j : ι) :
      f (s, r) ∉ W j ∧ f (r, s) ∉ W j := by
    obtain ⟨b, hb⟩ := hrow s r hr
    obtain ⟨a, ha⟩ := hcol s r hr
    have hmem {a b : WallComplement W} {y : V}
        (hy : y = AffineMap.lineMap a.val b.val (s : ℝ)) (hj : y ∈ W j) :
        (s : ℝ) ∈ Prod.snd '' WallComplement.crossings a b :=
      ⟨(j, s), (WallComplement.mem_crossings _ _ _ _).mpr ⟨s.property, hy ▸ hj⟩, rfl⟩
    exact ⟨fun hj => hs (Or.inl (mem_iUnion.mpr ⟨b, hmem hb hj⟩)),
      fun hj => hs (Or.inr (mem_iUnion.mpr ⟨a, hmem ha hj⟩))⟩
  -- Boundary edges are subsegments of the given sides.
  have hsub {a b : WallComplement W} (e : a ⟶ b) (g : unitInterval → V)
      (hg : ∀ s, g s = AffineMap.lineMap a.val b.val (s : ℝ)) (s₁ s₂ : unitInterval)
      (h₁ : ∀ j, g s₁ ∉ W j) (h₂ : ∀ j, g s₂ ∉ W j) : (g s₁, g s₂) ∈ admissiblePairs W :=
    (mem_admissiblePairs_iff ⟨g s₁, h₁⟩ ⟨g s₂, h₂⟩).mpr
      (e.down.subsegment s₁.property s₂.property (hg s₁) (hg s₂))
  have hside (s₁ s₂ r : unitInterval) (hr : r = 0 ∨ r = 1) (_ : s₁ ≤ s₂)
      (hs₁ : (s₁ : ℝ) ∉ S) (hs₂ : (s₂ : ℝ) ∉ S)
      (_ : ∀ τ ∈ (∅ : Finset unitInterval), τ ≤ s₁ ∨ s₂ ≤ τ) :
      (f (s₁, r), f (s₂, r)) ∈ admissiblePairs W ∧
        (f (r, s₁), f (r, s₂)) ∈ admissiblePairs W := by
    have hr' := hr
    rcases hr' with rfl | rfl
    · exact ⟨hsub (e₁ 0) (fun s => f (s, 0)) (fun s => by simpa using hf₁ 0 s) s₁ s₂
          (fun j => (hSside s₁ 0 hr hs₁ j).1) (fun j => (hSside s₂ 0 hr hs₂ j).1),
        hsub (e₂ 0) (fun s => f (0, s)) (fun s => by simpa using hf₂ 0 s) s₁ s₂
          (fun j => (hSside s₁ 0 hr hs₁ j).2) (fun j => (hSside s₂ 0 hr hs₂ j).2)⟩
    · exact ⟨hsub (e₁ 1) (fun s => f (s, 1)) (fun s => by simpa using hf₁ 1 s) s₁ s₂
          (fun j => (hSside s₁ 1 hr hs₁ j).1) (fun j => (hSside s₂ 1 hr hs₂ j).1),
        hsub (e₂ 1) (fun s => f (1, s)) (fun s => by simpa using hf₂ 1 s) s₁ s₂
          (fun j => (hSside s₁ 1 hr hs₁ j).2) (fun j => (hSside s₂ 1 hr hs₂ j).2)⟩
  obtain ⟨n, t, hn, ht0, htmono, ht1, -, rest⟩ :=
    exists_admissible_filling_grid_of_sides W hpoly hdim f S hS (hend 0 (Or.inl rfl))
      (hend 1 (Or.inr rfl)) hSside ∅ (by simp) hside U hU hcover hη
  exact ⟨n, t, hn, ht0, htmono, ht1, rest⟩

end Mei.Convex
