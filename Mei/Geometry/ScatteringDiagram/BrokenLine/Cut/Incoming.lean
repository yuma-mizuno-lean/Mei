/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut
public import Mei.Geometry.Convex.Sweep.Admissible.Terminal

/-!
# Uniform incoming cuts of decorated rays

Cutting just before a recorded encounter retains its complete incoming history,
whole decorations and incoming tail. For a fixed final encounter and prescribed
adjacent spatial velocities, the encounter position is independent of the history. One
sufficiently small positive displacement therefore gives an incoming endpoint
admitted by every outgoing ray in that finite fiber. This discharges the
incoming endpoint test when comparing weighted attachment fibers.

The displacement may depend on the outgoing endpoint and fiber. No genericity,
coefficient basis, positivity or nonzero spatial change is required. All source,
wall and singular avoidance conditions remain in the incoming domain; we do not
assert that every incoming ray extends across the encounter.

We use `DecoratedAdmissibleRay.truncate`, the straight incoming-segment formula,
and finiteness of whole-component histories. The incoming-cut argument extends
`CutoffDecoratedRay.eventually_exists_lastChange_incoming` to arbitrary block
boundaries before imposing positivity or a cutoff. Cutting before the last change is
part of the backward-ray recursion in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex
open scoped Topology

namespace Mei.DecoratedAdmissibleRay

section

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {m n : ℕ} {T : Fin (m + n) → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin (m + n) → V →L[ℝ] ℝ} {c : Fin (m + n) → ℝ}
  {ε : Fin (m + n) → SignType} {P : Fin (m + n) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- Immediately before any block boundary there is an actual incoming decorated
ray. It retains all older encounters, their translated parameters, their whole
decorations and the complete incoming path. The boundary can be the endpoint
itself or the beginning of the unbounded incoming segment. -/
theorem eventually_exists_incoming_truncate
    (r : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    let i := Fin.natAdd m (0 : Fin (n + 1))
    let b := Fin.snoc (α := fun _ => Γ) r.1.val p₀
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∃ s : DecoratedAdmissibleRay ℳ (fun j => T (Fin.natAdd m j)) p₀ a v
          (fun j => f (Fin.natAdd m j)) (fun j => c (Fin.natAdd m j))
          (fun j => ε (Fin.natAdd m j)) (fun j => P (Fin.natAdd m j))
          W S C (r.2.ray (r.2.parameter i) + η • v (b i)),
        s.1.val = (fun j => r.1.val (Fin.natAdd m j)) ∧
        (∀ j, s.decoration j = r.decoration (Fin.natAdd m j)) ∧
        (∀ j : Fin n, s.2.parameter j.succ =
          r.2.parameter (Fin.natAdd m j).succ - (r.2.parameter i - η)) ∧
        ∀ u ≤ 0, s.2.ray u = r.2.ray (u + (r.2.parameter i - η)) := by
  dsimp only
  let i := Fin.natAdd m (0 : Fin (n + 1))
  have hgap : ∀ᶠ η : ℝ in 𝓝 0, ∀ j : Fin (m + n + 1),
      i < j → r.2.parameter j < r.2.parameter i - η := by
    apply eventually_all.mpr
    intro j
    by_cases hj : i < j
    · have hlt := r.2.strictAnti_parameter hj
      filter_upwards [eventually_lt_nhds (sub_pos.mpr hlt)] with η hη _
      linarith
    · exact Eventually.of_forall fun _ h => (hj h).elim
  filter_upwards [hgap.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with η hη hpos
  have hpos : 0 < η := hpos
  have hu : r.2.parameter i - η < r.2.parameter i := sub_lt_self _ hpos
  have hl (j : Fin n) :
      r.2.parameter (Fin.natAdd m j).succ < r.2.parameter i - η := by
    apply hη _
    simp only [i, Fin.lt_def, Fin.val_natAdd, Fin.val_succ, Fin.val_zero, add_zero]
    omega
  have he : r.2.ray (r.2.parameter i - η) =
      r.2.ray (r.2.parameter i) +
        η • v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ i) := by
    simpa only [sub_sub_cancel] using
      r.2.ray_eq_add_smul_of_before_parameter i hu.le (fun j hj => (hη j hj).le)
  rw [← he]
  exact ⟨r.truncate _ hu hl, r.history_truncate _ hu hl,
    r.decoration_truncate _ hu hl, r.parameter_truncate_succ _ hu hl,
    fun u hu₀ => r.truncate_apply _ hu hl u hu₀⟩

local notation "E" => DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q

/-- For a straight terminal block with prescribed spatial velocities on its two sides,
one common positive displacement admits every outgoing history's incoming
part. The boundary point is the explicit intersection of the outgoing line
and the last discarded encounter's hyperplane. Later unchanged encounters
are retained in the outgoing fiber. The incoming endpoint test requires no
additional admission hypothesis, including for empty fibers and empty tails. -/
theorem eventually_forall_mem_admissibleBackwardDomain (j : Fin (m + n)) (hj : j.val + 1 = m)
    (p q : Γ) :
    let x := Q + ((c j - f j Q) / f j (v q)) • v q
    ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ r : E,
      (∀ l ≤ j.castSucc, v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ l) = v q) →
      v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ j.succ) = v p →
        x + η • v p ∈ admissibleBackwardDomain
          (fun l : Fin n => f (Fin.natAdd m l)) (fun l => c (Fin.natAdd m l))
          (fun l => v (Fin.snoc (α := fun _ => Γ)
            (fun z : Fin n => r.1.val (Fin.natAdd m z)) p₀ l))
          (fun l => P (Fin.natAdd m l)) W S C := by
  dsimp only
  have hi : j.succ = Fin.natAdd m (0 : Fin (n + 1)) := by
    apply Fin.ext
    simpa only [Fin.val_succ, Fin.val_natAdd, Fin.val_zero, add_zero] using hj
  apply eventually_all.mpr
  intro r
  -- Choose the cut bound before prescribing the two spatial velocities. Only the gaps
  -- between this ray's recorded parameters control how small it must be.
  filter_upwards [r.eventually_exists_incoming_truncate (m := m) (n := n)] with η hη hq hp
  have hzero := hq 0 (Fin.zero_le _)
  have ht := r.2.parameter_eq_div_of_directions_eq j
    (fun l hl => (hq l hl).trans hzero.symm)
  have hpoint := r.2.ray_eq_endpoint_sub_smul j.succ
    (fun l hl => (hq l (Fin.le_castSucc_iff.mpr hl)).trans hzero.symm)
    (t := r.2.parameter j.succ)
    ⟨le_rfl, by simpa only [r.2.parameter_zero] using
      r.2.strictAnti_parameter.antitone (Fin.zero_le j.succ)⟩
  rw [hzero] at ht hpoint
  have hx : r.2.ray (r.2.parameter j.succ) =
      Q + ((c j - f j Q) / f j (v q)) • v q := by
    rw [hpoint, ht]
    simp only [← neg_sub (c j) (f j Q), neg_div, neg_smul, sub_neg_eq_add]
  obtain ⟨s, hs, _, _, _⟩ := hη
  have hd := s.2.mem_admissibleBackwardDomain
  rw [hs] at hd
  simpa only [← hi, hx, hp] using hd

end

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V}

/-- A common sufficiently short incoming cut is admitted by the entire older
history of every ray with prescribed final adjacent degrees. The newly prepended
encounter is removed; arbitrary source and obstacle conditions persist. -/
theorem eventually_forall_mem_admissibleBackwardDomain_cons (U : Module.End R M) (p q : Γ)
    (Q : V) (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V) :
    let x := Q + ((b - m Q) / m (v q)) • v q
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∀ z : DecoratedAdmissibleRay ℳ (Fin.cons U T) p₀ a v
        (Fin.cons m f) (Fin.cons b c) (Fin.cons (SignType.sign (m (v q))) ε)
        (Fin.cons H P) W S C Q,
      z.1.val 0 = q →
      Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p →
      x + η • v p ∈ admissibleBackwardDomain f c
        (fun j => v (Fin.snoc (α := fun _ => Γ)
          (fun i : Fin n => z.1.val i.succ) p₀ j)) P W S C := by
  -- Transport the block-cutting theorem from `Fin (1 + n)` to the `Fin.cons`
  -- convention `Fin (n + 1)` before specializing the signed encounter data.
  have cut (N : ℕ) (hN : 1 + n = N)
      (T' : Fin N → Module.End R M) (f' : Fin N → V →L[ℝ] ℝ)
      (c' : Fin N → ℝ) (ε' : Fin N → SignType) (P' : Fin N → Set V) :
      let j := Fin.cast hN (0 : Fin (1 + n))
      let x := Q + ((c' j - f' j Q) / f' j (v q)) • v q
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        ∀ z : DecoratedAdmissibleRay ℳ T' p₀ a v f' c' ε' P' W S C Q,
        (∀ l ≤ j.castSucc, v (Fin.snoc (α := fun _ => Γ) z.1.val p₀ l) = v q) →
        v (Fin.snoc (α := fun _ => Γ) z.1.val p₀ j.succ) = v p →
        x + η • v p ∈ admissibleBackwardDomain
          (fun i => f' (Fin.cast hN (Fin.natAdd 1 i)))
          (fun i => c' (Fin.cast hN (Fin.natAdd 1 i)))
          (fun j => v (Fin.snoc (α := fun _ => Γ)
            (fun i : Fin n => z.1.val (Fin.cast hN (Fin.natAdd 1 i))) p₀ j))
          (fun i => P' (Fin.cast hN (Fin.natAdd 1 i))) W S C := by
    subst N
    exact eventually_forall_mem_admissibleBackwardDomain
      (m := 1) (n := n) 0 rfl p q
  have hh := cut (n + 1) (Nat.add_comm 1 n) (Fin.cons U T) (Fin.cons m f) (Fin.cons b c)
    (Fin.cons (SignType.sign (m (v q))) ε) (Fin.cons H P)
  have hind (j : Fin n) :
      Fin.cast (Nat.add_comm 1 n) (Fin.natAdd 1 j) = j.succ := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
    omega
  have hzero : Fin.cast (Nat.add_comm 1 n) (0 : Fin (1 + n)) = 0 := by
    apply Fin.ext
    rfl
  simp only [hzero, hind, Fin.cons_zero, Fin.cons_succ] at hh
  filter_upwards [hh] with η hη z hq hp
  have hsnoc : Fin.snoc (α := fun _ => Γ) z.1.val p₀ (0 : Fin (n + 1)).succ =
      Fin.snoc (α := fun _ => Γ) (fun i : Fin n => z.1.val i.succ) p₀ 0 := by
    rw [← Fin.cons_self_tail z.1.val, ← Fin.cons_snoc_eq_snoc_cons]
    rfl
  exact hη z (fun l hl => by
    have hl : l = 0 := by simpa using hl
    subst l
    simpa using congrArg v hq) (by rw [hsnoc]; exact congrArg v hp)

end Mei.DecoratedAdmissibleRay
