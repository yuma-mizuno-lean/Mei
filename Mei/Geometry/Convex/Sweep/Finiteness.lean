/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Realization
public import Mei.Algebra.PositiveDegrees.Basic
public import Mathlib.Data.Set.Finite.List
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finiteness of realized degree itineraries

A transverse backward itinerary records a relative degree and a wall at every
encounter, including encounters that preserve the decoration's degree. Relative
degrees decrease in a positive monoid as we move backwards from the endpoint.
If a degree occurs twice, every intermediate degree is equal to it. Those
encounters therefore lie on a single straight segment, on which a transverse
hyperplane can occur at most once. Consequently the degree-wall pairs have no
repetitions.

At a fixed degree cutoff and for finitely many walls, there are only finitely
many such lists across all endpoints. No bound on the number of encounters is
assumed. This supplies the geometric finiteness needed in addition to bounds on
nonzero component changes; changes of zero spatial direction remain distinct
relative degrees. Selected polyhedral supports, avoidance, incoming admission,
and coefficient propagation can restrict this finite set further.

We use `backwardPoint_eq_add_of_constant` and the finite cutoffs of
`PositiveDegrees`. The backward parameterization and finite-type argument follow
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2), and Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.Convex

open Set

variable {Γ V J : Type*} [AddCommGroup Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (d : PositiveDegrees Γ) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (v : Γ → V)

/-- Degree-wall lists realized by transverse positive-time backward propagation.
The first component of each entry is its relative degree on the segment leading
backwards to that wall. Degrees decrease by allowed increments and lie in the
fixed cutoff. Every encounter is retained, even without a degree change.
The velocity may depend on the initial degree through the choice of `v`. -/
def realizedDegreeItineraries (k : ℕ) : Set (List (Γ × J)) :=
  {l | (∀ a ∈ l, a.1 ∈ d.cutoff k ∧ f a.2 (v a.1) ≠ 0) ∧
    (∀ a b : Fin l.length, a ≤ b → (l.get a).1 - (l.get b).1 ∈ d.monoid) ∧
    ∃ Q : V, ∀ a : Fin l.length,
      0 < backwardTime (fun j => f (l.get j).2) (fun j => c (l.get j).2)
        (fun j => v (l.get j).1) a Q}

/-- Membership separates the cutoff, transversality, decreasing-degree and
positive-time realization conditions. Hyperplane incidence follows from
transversality and `backwardPoint_height`. -/
@[simp]
theorem mem_realizedDegreeItineraries (k : ℕ) (l : List (Γ × J)) :
    l ∈ realizedDegreeItineraries d f c v k ↔
      (∀ a ∈ l, a.1 ∈ d.cutoff k ∧ f a.2 (v a.1) ≠ 0) ∧
      (∀ a b : Fin l.length, a ≤ b → (l.get a).1 - (l.get b).1 ∈ d.monoid) ∧
      ∃ Q : V, ∀ a : Fin l.length,
        0 < backwardTime (fun j => f (l.get j).2) (fun j => c (l.get j).2)
          (fun j => v (l.get j).1) a Q := Iff.rfl

/-- Enlarging the relative-degree cutoff retains every realized itinerary. -/
theorem realizedDegreeItineraries_mono : Monotone (realizedDegreeItineraries d f c v) := by
  intro k l hkl L hL
  exact ⟨fun a ha => ⟨d.cutoff_mono hkl (hL.1 a ha).1, (hL.1 a ha).2⟩,
    hL.2⟩

/-- A positive-time transverse itinerary with decreasing relative degrees cannot
repeat a degree-wall pair. Constant-degree encounters are bounded geometrically,
rather than discarded as artificial subdivisions. -/
theorem nodup_of_mem_realizedDegreeItineraries {k : ℕ} {l : List (Γ × J)}
    (hl : l ∈ realizedDegreeItineraries d f c v k) : l.Nodup := by
  obtain ⟨hmem, hdegree, Q, hpos⟩ := hl
  let F (j : Fin l.length) := f (l.get j).2
  let C (j : Fin l.length) := c (l.get j).2
  let U (j : Fin l.length) := v (l.get j).1
  have htrans (j : Fin l.length) : F j (U j) ≠ 0 :=
    (hmem _ (List.get_mem l j)).2
  have hne {a b : Fin l.length} (hab : a < b) : l.get a ≠ l.get b := by
    intro he
    have hq : (l.get a).1 = (l.get b).1 := congrArg Prod.fst he
    have hwall : (l.get a).2 = (l.get b).2 := congrArg Prod.snd he
    have hconstant (j : Fin l.length) (haj : a.succ ≤ j.castSucc)
        (hjb : j.succ ≤ b.succ) : U j = U a := by
      have haj' : a ≤ j := by
        simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at haj ⊢
        omega
      have hjb' : j ≤ b := by simpa using hjb
      have hneg : -((l.get a).1 - (l.get j).1) ∈ d.monoid := by
        simpa only [neg_sub, hq] using hdegree j b hjb'
      exact congrArg v (sub_eq_zero.mp
        (d.eq_zero_of_mem_of_neg_mem (hdegree a j haj') hneg)).symm
    have hline := backwardPoint_eq_add_of_constant F C U Q a.succ b.succ
      (by simpa using hab.le) (U a) hconstant
    have ha := backwardPoint_height F C U a (htrans a) Q
    have hb := backwardPoint_height F C U b (htrans b) Q
    have hsame : F a = F b := congrArg f hwall
    have hlevel : C a = C b := congrArg c hwall
    have hheight : F a (backwardPoint F C U b.succ Q) = C a := by
      rw [hsame, hlevel]
      exact hb
    rw [hline, map_add, map_smul, smul_eq_mul, ha] at hheight
    have ht := strictAnti_backwardParameter F C U Q hpos (Fin.succ_lt_succ_iff.mpr hab)
    exact (mul_ne_zero (sub_pos.mpr ht).ne' (htrans a)) (by linarith)
  apply List.nodup_iff_injective_get.mpr
  intro a b he
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (hne hab he).elim
  · exact hab
  · exact (hne hab he.symm).elim

/-- Actual transverse encounters with positive elapsed times give one of the
realized lists. The recurrence and incidences determine the backward formulas;
the caller need not describe its geometry using those formulas. -/
theorem mem_realizedDegreeItineraries_of_encounters (k : ℕ) (l : List (Γ × J))
    (hmem : ∀ a ∈ l, a.1 ∈ d.cutoff k ∧ f a.2 (v a.1) ≠ 0)
    (hdegree : ∀ a b : Fin l.length,
      a ≤ b → (l.get a).1 - (l.get b).1 ∈ d.monoid)
    (X : Fin (l.length + 1) → V) (t : Fin l.length → ℝ)
    (hpos : ∀ a, 0 < t a)
    (hstep : ∀ a, X a.succ = X a.castSucc + t a • v (l.get a).1)
    (hheight : ∀ a, f (l.get a).2 (X a.succ) = c (l.get a).2) :
    l ∈ realizedDegreeItineraries d f c v k := by
  have ht := (backward_unique (fun a => f (l.get a).2) (fun a => c (l.get a).2)
    (fun a => v (l.get a).1) (fun a => (hmem _ (List.get_mem l a)).2)
    (X 0) X t rfl hstep hheight).2
  exact ⟨hmem, hdegree, X 0, fun a => (ht a) ▸ hpos a⟩

/-- The number of encounters is at most the number of retained degree-wall
pairs. No encounter count or distinctness hypothesis is assumed. -/
theorem length_le_card_of_mem_realizedDegreeItineraries [Finite J]
    {k : ℕ} {l : List (Γ × J)} (hl : l ∈ realizedDegreeItineraries d f c v k) :
    l.length ≤ Nat.card (d.cutoff k) * Nat.card J := by
  let lift (a : Fin l.length) : d.cutoff k × J :=
    (⟨(l.get a).1, (hl.1 _ (List.get_mem l a)).1⟩, (l.get a).2)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply (nodup_of_mem_realizedDegreeItineraries d f c v hl).injective_get
    exact Prod.ext (congrArg (fun x : d.cutoff k × J => x.1.val) hab)
      (congrArg (fun x : d.cutoff k × J => x.2) hab)
  simpa only [Nat.card_fin, Nat.card_prod] using Nat.card_le_card_of_injective lift hinj

/-- At any fixed order, only finitely many transverse decreasing-degree
itineraries are realized, even as the endpoint varies over the entire space.
Additional support, incoming-tail and coefficient constraints select a subset. -/
theorem finite_realizedDegreeItineraries [Finite J] (k : ℕ) :
    (realizedDegreeItineraries d f c v k).Finite := by
  apply ((List.finite_length_le (d.cutoff k × J)
    (Nat.card (d.cutoff k) * Nat.card J)).image
      (fun L => L.map (fun a => (a.1.val, a.2)))).subset
  intro l hl
  let L : List (d.cutoff k × J) := l.attach.map fun a =>
    (⟨a.val.1, (hl.1 a.val a.property).1⟩, a.val.2)
  refine ⟨L, ?_, ?_⟩
  · simpa only [Set.mem_ofPred_eq, L, List.length_map, List.length_attach] using
      length_le_card_of_mem_realizedDegreeItineraries d f c v hl
  · simp only [L, List.map_map, Function.comp_def]
    exact List.attach_map_subtype_val l

/-- Realized lists can index finite endpoint families without an assumed bound
on their number of encounters. -/
instance [Finite J] (k : ℕ) : Finite (realizedDegreeItineraries d f c v k) :=
  (finite_realizedDegreeItineraries d f c v k).to_subtype

end Mei.Convex
