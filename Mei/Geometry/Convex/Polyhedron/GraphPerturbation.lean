/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.SimultaneousPath

/-!
# Relative perturbation of finite polygonal graphs

A finite family of free vertices can be chosen in prescribed open sets so that
all segments involving a free vertex are admissible for a finite polyhedral
wall family. Prescribed fixed vertices remain unchanged. Consequently a finite
graph whose edges between fixed vertices are already admissible admits
arbitrarily small vertex perturbations making every edge admissible.

This supplies relative general position for the edges of a polygonal mesh:
its boundary vertices can be fixed while its interior vertices move. No
embedding or distinctness assumption is imposed on the vertex positions.
The construction iterates `WallComplement.exists_mem_open_admissible_spokes`.
-/

public section

open Set

namespace Mei.Convex

variable {V ι A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι]
  (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
  (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)

include hpoly hdim

open Classical in
/-- Choose the vertices indexed by `T` in prescribed open sets, retaining all
other positions. Every segment involving a newly chosen vertex and any vertex
indexed by `S ∪ T` is admissible. Original positions indexed by `S` avoid the walls. -/
theorem exists_mem_open_admissible_vertices
    (x : A → V) (S T : Finset A)
    (hfixed : ∀ a ∈ S, ∀ i, x a ∉ W i) (U : A → Set V)
    (hU : ∀ a ∈ T, IsOpen (U a)) (hne : ∀ a ∈ T, (U a).Nonempty) :
    ∃ y : A → V, (∀ a ∉ T, y a = x a) ∧ (∀ a ∈ T, y a ∈ U a) ∧
      (∀ a ∈ S ∪ T, ∀ i, y a ∉ W i) ∧
      ∀ a ∈ S ∪ T, ∀ b ∈ S ∪ T, a ∈ T ∨ b ∈ T →
        (y a, y b) ∈ admissiblePairs W := by
  classical
  -- Insert one free vertex at a time, connecting it to the entire previously chosen family.
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨x, by simp, by simp, ?_, by simp⟩
    simpa using hfixed
  | @insert a T ha ih =>
    obtain ⟨y, hyfix, hyU, hyallowed, hypairs⟩ := ih
      (fun b hb => hU b (Finset.mem_insert_of_mem hb))
      (fun b hb => hne b (Finset.mem_insert_of_mem hb))
    let p : (S ∪ T : Finset A) → WallComplement W :=
      fun b => ⟨y b, hyallowed b b.property⟩
    obtain ⟨z, hzU, hz⟩ := WallComplement.exists_mem_open_admissible_spokes W hpoly hdim p
      (hU a (Finset.mem_insert_self a T)) (hne a (Finset.mem_insert_self a T))
    refine ⟨Function.update y a z.val, ?_, ?_, ?_, ?_⟩
    · intro b hb
      have hba : b ≠ a := by intro he; subst b; simp at hb
      simpa [hba] using hyfix b (fun ht => hb (Finset.mem_insert_of_mem ht))
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa using hzU
      · have hba : b ≠ a := by intro he; subst b; exact ha hb
        simpa [hba] using hyU b hb
    · intro b hb i
      by_cases hba : b = a
      · subst b
        simpa using z.notMem i
      · have hb' : b ∈ S ∪ T := by simpa [hba] using hb
        simpa [hba] using hyallowed b hb' i
    -- Only incidences involving the new vertex need new segments.
    · intro b hb c hc hfree
      by_cases hba : b = a
      · subst b
        by_cases hca : c = a
        · subst c
          have hregular : z.val ∉ singularSupport W := by
            intro hs
            obtain ⟨i, hi⟩ := mem_iUnion.mp
              (singularSupport_subset_iUnion W (fun i => (hpoly i).isClosed) hs)
            exact z.notMem i hi
          simpa using (mem_admissiblePairs_iff z z).mpr (.refl z hregular)
        · have hc' : c ∈ S ∪ T := by simpa [hca] using hc
          obtain ⟨e⟩ := hz ⟨c, hc'⟩
          simpa [hca, p] using (mem_admissiblePairs_iff z (p ⟨c, hc'⟩)).mpr e.down
      · by_cases hca : c = a
        · subst c
          have hb' : b ∈ S ∪ T := by simpa [hba] using hb
          obtain ⟨e⟩ := hz ⟨b, hb'⟩
          simpa [hba, p] using (mem_admissiblePairs_iff (p ⟨b, hb'⟩) z).mpr e.down.symm
        · have hb' : b ∈ S ∪ T := by simpa [hba] using hb
          have hc' : c ∈ S ∪ T := by simpa [hca] using hc
          have hf : b ∈ T ∨ c ∈ T := by simpa [hba, hca] using hfree
          simpa [hba, hca] using hypairs b hb' c hc' hf

open Classical in
/-- Perturb the vertices of any finite directed graph, fixing a prescribed
subset and retaining its edges. Original free vertices may lie on walls.
All perturbed vertices avoid the walls and all graph edges become admissible;
only edges between fixed vertices must be admissible initially. -/
theorem exists_admissible_graph_perturbation [Finite A]
    (x : A → V) (r : A → A → Prop) (S : Finset A)
    (hfixed : ∀ a ∈ S, ∀ i, x a ∉ W i)
    (hedge : ∀ a ∈ S, ∀ b ∈ S, r a b → (x a, x b) ∈ admissiblePairs W)
    (ε : A → ℝ) (hε : ∀ a, 0 < ε a) :
    ∃ y : A → V, (∀ a ∈ S, y a = x a) ∧ (∀ a, dist (y a) (x a) < ε a) ∧
      (∀ a i, y a ∉ W i) ∧ ∀ a b, r a b → (y a, y b) ∈ admissiblePairs W := by
  classical
  let := Fintype.ofFinite A
  obtain ⟨y, hyfix, hyball, hyallowed, hypairs⟩ :=
    exists_mem_open_admissible_vertices W hpoly hdim x S (Finset.univ \ S)
      hfixed (fun a => Metric.ball (x a) (ε a))
      (fun _ _ => Metric.isOpen_ball) (fun a _ => Metric.nonempty_ball.mpr (hε a))
  have hsame (a) (ha : a ∈ S) : y a = x a := hyfix a (by simp [ha])
  refine ⟨y, hsame, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ S
    · simpa [hsame a ha] using hε a
    · exact hyball a (by simp [ha])
  · intro a i
    exact hyallowed a (by simp) i
  · intro a b hab
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · simpa only [hsame a ha, hsame b hb] using hedge a ha b hb hab
      · exact hypairs a (by simp) b (by simp) (Or.inr (by simp [hb]))
    · exact hypairs a (by simp) b (by simp) (Or.inl (by simp [ha]))

end Mei.Convex
