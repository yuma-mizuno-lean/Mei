/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Adjacency of actual connected components

The vertices are Mathlib's connected components of a subset. Two distinct
components are adjacent when their ambient closures share a point of a
specified regular set. A continuous curve lying in the regular set and leaving
the subset only at finitely many parameters gives an actual finite graph walk.

The proof isolates one exceptional parameter and uses connected images of
half-open intervals on its two sides. Their common limiting point belongs to
both component closures. Erasing that parameter gives a finite induction.
No local connectedness or separation assumption on the ambient space is needed.
-/

public section

open Set

namespace ConnectedComponents

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- The ambient carrier of a connected component of a subset. -/
def carrier (c : ConnectedComponents s) : Set X :=
  Subtype.val '' {x : s | ConnectedComponents.mk x = c}

/-- At a represented component the carrier is the actual `connectedComponentIn`. -/
theorem carrier_mk (x : s) :
    (ConnectedComponents.mk x).carrier = connectedComponentIn s x.val := by
  rw [carrier, connectedComponentIn_eq_image x.property]
  congr 1
  ext y
  exact ConnectedComponents.coe_eq_coe'

/-- Equality of component vertices is membership in the ambient component carrier. -/
theorem mk_eq_mk_iff_mem_connectedComponentIn {x y : s} :
    ConnectedComponents.mk x = ConnectedComponents.mk y ↔
      x.val ∈ connectedComponentIn s y.val := by
  rw [← carrier_mk y]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := Subtype.ext hzx
    change ConnectedComponents.mk z = ConnectedComponents.mk y at hz
    simpa only [hzx'] using hz

end ConnectedComponents

namespace Mei

variable {X : Type*} [TopologicalSpace X]

/-- The graph of actual components, with adjacency witnessed by a common
ambient closure point in the prescribed regular set. -/
def componentAdjacencyGraph (s R : Set X) : SimpleGraph (ConnectedComponents s) where
  Adj c d := c ≠ d ∧ ∃ x ∈ R, x ∈ closure c.carrier ∧ x ∈ closure d.carrier
  symm := ⟨fun _ _ ⟨hne, x, hx, hc, hd⟩ => ⟨hne.symm, x, hx, hd, hc⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Adjacency is exactly a regular common closure point between distinct components. -/
theorem componentAdjacencyGraph_adj {s R : Set X} {c d : ConnectedComponents s} :
    (componentAdjacencyGraph s R).Adj c d ↔
      c ≠ d ∧ ∃ x ∈ R, x ∈ closure c.carrier ∧ x ∈ closure d.carrier := Iff.rfl

/-- A continuous curve with only finitely many exceptional parameters gives
a finite adjacency walk between its endpoint components. Every parameter of
the curve lies in the regular set, so all adjacency witnesses are regular.
The curve may be constant and the endpoints may belong to the same component. -/
theorem componentAdjacencyGraph_reachable_of_finite_exceptions
    {s R : Set X} {f : ℝ → X} (T : Finset ℝ)
    {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (ha : f a ∈ s) (hb : f b ∈ s)
    (hR : ∀ t ∈ Icc a b, f t ∈ R)
    (hT : ∀ t ∈ Icc a b, f t ∉ s → t ∈ T) :
    (componentAdjacencyGraph s R).Reachable
      (ConnectedComponents.mk ⟨f a, ha⟩) (ConnectedComponents.mk ⟨f b, hb⟩) := by
  classical
  induction T using Finset.strongInductionOn generalizing a b with
  | _ T ih =>
    by_cases hall : ∀ t ∈ Icc a b, f t ∈ s
    · have hconn : IsPreconnected (f '' Icc a b) :=
        isPreconnected_Icc.image f hf
      have hsub : f '' Icc a b ⊆ s := by
        rintro _ ⟨t, ht, rfl⟩
        exact hall t ht
      have hmem : f b ∈ connectedComponentIn s (f a) :=
        hconn.subset_connectedComponentIn ⟨a, ⟨le_rfl, hab⟩, rfl⟩ hsub
          ⟨b, ⟨hab, le_rfl⟩, rfl⟩
      have heq := (ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn
        (x := (⟨f b, hb⟩ : s)) (y := ⟨f a, ha⟩)).mpr hmem
      rw [heq]
    · push Not at hall
      obtain ⟨t, ht, hbad⟩ := hall
      have htT : t ∈ T := hT t ht hbad
      have hat : a < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact hbad ha)
      have htb : t < b := lt_of_le_of_ne ht.2 (by rintro rfl; exact hbad hb)
      have hnot : t ∈ ((T.erase t : Finset ℝ) : Set ℝ)ᶜ := by simp
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (T.erase t).isClosed.isOpen_compl t hnot
      let δ := min r (min (t - a) (b - t)) / 2
      have hδ : 0 < δ := half_pos (lt_min hr (lt_min (sub_pos.mpr hat) (sub_pos.mpr htb)))
      have hδr : δ < r := by
        have := min_le_left r (min (t - a) (b - t))
        dsimp only [δ]
        linarith
      have hδa : δ < t - a := by
        have := (min_le_right r (min (t - a) (b - t))).trans (min_le_left _ _)
        dsimp only [δ]
        linarith
      have hδb : δ < b - t := by
        have := (min_le_right r (min (t - a) (b - t))).trans (min_le_right _ _)
        dsimp only [δ]
        linarith
      have hleft : a ≤ t - δ := by linarith
      have hright : t + δ ≤ b := by linarith
      have hlocal (u : ℝ) (hu : u ∈ Icc (t - δ) (t + δ)) (hut : u ≠ t) : f u ∈ s := by
        by_contra hus
        have huT : u ∈ T := hT u ⟨by linarith [hu.1], by linarith [hu.2]⟩ hus
        have huball : u ∈ Metric.ball t r := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith [hu.1, hu.2]
        exact hball huball (Finset.mem_erase.mpr ⟨hut, huT⟩)
      have hs : f (t - δ) ∈ s := hlocal _ ⟨le_rfl, by linarith⟩ (by linarith)
      have hu : f (t + δ) ∈ s := hlocal _ ⟨by linarith, le_rfl⟩ (by linarith)
      have hbefore := ih (T.erase t) (Finset.erase_ssubset htT)
        (hf.mono (fun u hu => ⟨hu.1, by linarith [hu.2]⟩)) (by linarith : a ≤ t - δ)
        ha hs (fun u hu => hR u ⟨hu.1, by linarith [hu.2]⟩)
        (fun u hu hus => Finset.mem_erase.mpr
          ⟨by linarith [hu.2], hT u ⟨hu.1, by linarith [hu.2]⟩ hus⟩)
      have hafter := ih (T.erase t) (Finset.erase_ssubset htT)
        (hf.mono (fun u hu => ⟨by linarith [hu.1], hu.2⟩)) (by linarith : t + δ ≤ b)
        hu hb (fun u hu => hR u ⟨by linarith [hu.1], hu.2⟩)
        (fun u hu hus => Finset.mem_erase.mpr
          ⟨by linarith [hu.1], hT u ⟨by linarith [hu.1], hu.2⟩ hus⟩)
      have hcl : f t ∈ closure (connectedComponentIn s (f (t - δ))) := by
        have hsub : f '' Ico (t - δ) t ⊆ connectedComponentIn s (f (t - δ)) := by
          apply (isPreconnected_Ico.image f (hf.mono (fun u hu =>
            ⟨by linarith [hu.1], by linarith [hu.2]⟩))).subset_connectedComponentIn
            ⟨t - δ, ⟨le_rfl, by linarith⟩, rfl⟩
          rintro _ ⟨u, hu, rfl⟩
          exact hlocal u ⟨hu.1, by linarith [hu.2]⟩ hu.2.ne
        apply closure_mono hsub
        apply mem_closure_image (hf.continuousAt (Icc_mem_nhds hat htb))
        rw [closure_Ico (by linarith : t - δ ≠ t)]
        exact ⟨by linarith, le_rfl⟩
      have hcr : f t ∈ closure (connectedComponentIn s (f (t + δ))) := by
        have hsub : f '' Ioc t (t + δ) ⊆ connectedComponentIn s (f (t + δ)) := by
          apply (isPreconnected_Ioc.image f (hf.mono (fun u hu =>
            ⟨by linarith [hu.1], by linarith [hu.2]⟩))).subset_connectedComponentIn
            ⟨t + δ, ⟨by linarith, le_rfl⟩, rfl⟩
          rintro _ ⟨u, hu, rfl⟩
          exact hlocal u ⟨by linarith [hu.1], hu.2⟩ hu.1.ne'
        apply closure_mono hsub
        apply mem_closure_image (hf.continuousAt (Icc_mem_nhds hat htb))
        rw [closure_Ioc (by linarith : t ≠ t + δ)]
        exact ⟨le_rfl, by linarith⟩
      have hmiddle : (componentAdjacencyGraph s R).Reachable
          (ConnectedComponents.mk ⟨f (t - δ), hs⟩) (ConnectedComponents.mk ⟨f (t + δ), hu⟩) := by
        by_cases heq : ConnectedComponents.mk (⟨f (t - δ), hs⟩ : s) =
            ConnectedComponents.mk (⟨f (t + δ), hu⟩ : s)
        · rw [heq]
        · apply SimpleGraph.Adj.reachable
          apply componentAdjacencyGraph_adj.mpr
          exact ⟨heq, f t, hR t ht,
            by rwa [ConnectedComponents.carrier_mk], by rwa [ConnectedComponents.carrier_mk]⟩
      exact hbefore.trans (hmiddle.trans hafter)

end Mei
