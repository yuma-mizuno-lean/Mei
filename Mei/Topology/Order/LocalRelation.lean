/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Gluing local relations along a real interval

A relation on a dense set of allowed parameters extends along a compact interval
if it holds locally around every parameter and composes at allowed intermediate
parameters. The local neighborhoods include parameters outside the dense set.
This permits integration of local identities across finitely many excluded
crossing parameters, while keeping every subdivision vertex allowed.

The construction uses Mathlib's metric Lebesgue number lemma and
`Dense.exists_between`.
-/

public section

open Set Metric

/-- A locally valid relation on a dense set composes along a real interval.
Only increasing triples of allowed parameters in the interval need satisfy
the composition law. Local validity is required around every point of the
interval, including excluded parameters. -/
theorem Dense.rel_of_locally {s : Set ℝ} (hs : Dense s) {a b : ℝ}
    (hab : a ≤ b) (ha : a ∈ s) (hb : b ∈ s) (r : ℝ → ℝ → Prop)
    (hcomp : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      x ∈ s → y ∈ s → z ∈ s → x ≤ y → y ≤ z → r x y → r y z → r x z)
    (hlocal : ∀ t ∈ Icc a b, ∃ ε > 0,
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
        x ∈ ball t ε → y ∈ ball t ε → x ∈ s → y ∈ s → x ≤ y → r x y) :
    r a b := by
  classical
  choose ε hε hrel using fun t : Icc a b => hlocal t t.property
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (c := fun t : Icc a b => ball t.val (ε t)) (fun _ => isOpen_ball)
    (fun t ht => mem_iUnion.mpr ⟨⟨t, ht⟩, mem_ball_self (hε ⟨t, ht⟩)⟩)
  have hsmall (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
      (hxs : x ∈ s) (hys : y ∈ s) (hxy : x ≤ y) (hlen : y - x < δ) : r x y := by
    obtain ⟨t, ht⟩ := hcover x hx
    exact hrel t x hx y hy (ht (mem_ball_self hδ))
      (ht (by rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)]; exact hlen))
      hxs hys hxy
  let d := δ / 3
  have hd : 0 < d := by dsimp [d]; positivity
  have hstep (n : ℕ) : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      x ∈ s → y ∈ s → x ≤ y → y - x ≤ n * d → r x y := by
    induction n with
    | zero =>
      intro x hx y hy hxs hys hxy hlen
      have hlen : y - x ≤ 0 := by simpa using hlen
      exact hsmall x y hx hy hxs hys hxy (hlen.trans_lt hδ)
    | succ n ih =>
      intro x hx y hy hxs hys hxy hlen
      by_cases hshort : y - x ≤ 2 * d
      · exact hsmall x y hx hy hxs hys hxy (by dsimp [d] at hshort; linarith)
      obtain ⟨z, hzs, hzlo, hzhi⟩ := hs.exists_between (by linarith : x + d < x + 2 * d)
      have hxz : x ≤ z := by linarith
      have hzy : z ≤ y := by linarith
      have hz : z ∈ Icc a b := ⟨hx.1.trans hxz, hzy.trans hy.2⟩
      exact hcomp x hx z hz y hy hxs hzs hys hxz hzy
        (hsmall x z hx hz hxs hzs hxz (by dsimp [d] at hzhi; linarith))
        (ih z hz y hy hzs hys hzy (by push_cast at hlen; nlinarith))
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / d)
  exact hstep n a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ ha hb hab
    ((div_lt_iff₀ hd).mp hn).le
