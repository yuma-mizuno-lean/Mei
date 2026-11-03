/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Attachment.Incoming
public import Mei.Geometry.Convex.Sweep.Admissible.FinalEncounter
public import Mei.Data.Fin.Tuple

/-!
# Decomposing a cutoff evaluation by its final encounter

Fix a degree `q ≠ 0` and an endpoint `Q`, and suppose that the backward line
`Q + s • v q` first meets the wall supports at a single regular transverse encounter
`w`, at ray parameter `t`. Every cutoff ray of final degree `q` then ends with the
encounter `w`, the one nearest its endpoint, preceded by a segment of some degree
`p`. Hence, for all sufficiently short incoming displacements `η`, the degree-`q`
component of the full weighted evaluation at `Q` is the sum over the adjacent
degrees `p` of the degree-`q` component of the wall action `T w` applied to the
degree-`p` evaluation at the incoming germ `Q + t • v q + η • v p`.

The degree `p = q` of a changeless encounter is included, since such an encounter is
still recorded. Adjacent degrees whose normal velocities differ at `w` do not occur.
All encounter words, whole decorations, and the incoming tails and sources of the
older rays are retained. The argument needs neither genericity of `Q` nor any
property of the propagation maps. If the line has no encounter at all, the
degree-`q` component vanishes.

This is the nearest-encounter step of the backward-ray recursion in Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

/-- A ray whose final encounter is `w`, with degree `p` immediately before and `q`
immediately after it. -/
private def IsFinalEncounter (w : J) (p q : Γ)
    (z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) : Prop :=
  match z with
  | ⟨[], _, _, _⟩ => False
  | ⟨j :: l, z, _, _⟩ => j = w ∧ z.1.val 0 = q ∧
    Fin.snoc (α := fun _ => Γ) (fun i : Fin l.length => z.1.val i.succ) 0 0 = p

section Decomposition

variable (w : J) (q : Γ) (t : ℝ)

/-- The structure of a ray of final degree `q`: its final encounter is `w`. The
adjacent degree `p` before it survives the cutoff and has increment `q - p` in the
positive monoid, and `w` preserves the normal velocity from `p` to `q`. -/
private theorem exists_isFinalEncounter
    (hq : q ∈ d.cutoff k) (hq0 : q ≠ 0) (hP : ∀ j, P j ⊆ ⋃ b, W b)
    (ht : 0 < t) (hinc : Q + t • v q ∈ P w)
    (hW : ∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ W j)
    (hunique : ∀ e, f e (v q) ≠ 0 → SignType.sign (f e (v q)) = ε e →
      f e (Q + t • v q) = c e → Q + t • v q ∈ P e → e = w)
    (z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) (hz : z.finalDegree = q) :
    ∃ p, IsFinalEncounter w p q z ∧ p ∈ d.cutoff k ∧ q - p ∈ d.monoid ∧
      f w (v q) = f w (v p) := by
  rcases z with ⟨_ | ⟨e, l⟩, ρ, hm, hmono⟩
  · exact (hq0 (by simpa only [finalDegree_def, Fin.snoc_zero] using hz.symm)).elim
  · have hq' : ρ.1.val 0 = q := by
      simpa only [finalDegree_def, ← Fin.castSucc_zero, Fin.snoc_castSucc] using hz
    obtain ⟨htrans, τ, hτ, -, hheight, hmem, havoid⟩ := ρ.2.exists_finalEncounter
    have hdeg : Fin.snoc (α := fun _ => Γ) ρ.1.val 0 0 = q := by
      simpa only [finalDegree_def] using hz
    rw [hdeg] at htrans hheight hmem havoid
    have hsign : SignType.sign (f e (v q)) = ε e := by
      simpa only [hq', List.get_cons_zero] using ρ.crossing_sign 0
    have hew : e = w := by
      rcases lt_trichotomy τ t with hlt | rfl | hgt
      · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hP e hmem)
        exact (hW b (-τ) (by linarith) (by linarith)
          (by simpa only [neg_smul, sub_neg_eq_add] using hb)).elim
      · exact hunique e htrans hsign hheight hmem
      · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hP w hinc)
        exact (havoid b t ht.le hgt hb).elim
    subst hew
    have hnext := Fin.snoc_succ ρ.1.val 0 0
    have hsub : q - Fin.snoc (α := fun _ => Γ) ρ.1.val 0 (Fin.succ 0) ∈ d.monoid := by
      rcases Fin.eq_castSucc_or_eq_last (Fin.succ (0 : Fin (l.length + 1))) with ⟨j, hj⟩ | hj
      · rw [hj, Fin.snoc_castSucc, ← hq']
        exact hmono 0 j (Fin.zero_le j)
      · have h0 : Fin.snoc (α := fun _ => Γ) ρ.1.val 0 (Fin.last (l.length + 1)) = 0 :=
          Fin.snoc_last ..
        rw [hj, h0, sub_zero]
        exact (d.mem_cutoff.mp hq).1
    refine ⟨Fin.snoc (α := fun _ => Γ) (fun i : Fin l.length => ρ.1.val i.succ) 0 0,
      ⟨rfl, hq', rfl⟩, ?_, ?_, ?_⟩
    · have hcut : ∀ i, Fin.snoc (α := fun _ => Γ) ρ.1.val 0 i ∈ d.cutoff k :=
        Fin.lastCases (by simp) (fun j => by simpa only [Fin.snoc_castSucc] using hm j)
      rw [← hnext]
      exact hcut _
    · rwa [← hnext]
    · rw [← hnext, ← hq']
      simpa only [List.get_cons_zero] using ρ.normal_velocity_eq 0

/-- The final encounter fixes the degree before it. -/
private theorem IsFinalEncounter.unique {p p' : Γ}
    {z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q}
    (h : IsFinalEncounter w p q z) (h' : IsFinalEncounter w p' q z) : p = p' := by
  rcases z with ⟨_ | ⟨e, l⟩, ρ, hm, hmono⟩
  · exact h.elim
  · exact h.2.2.symm.trans h'.2.2

/-- A ray whose final encounter leads into degree `q` has final degree `q`. -/
private theorem IsFinalEncounter.finalDegree_eq {p : Γ}
    {z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q}
    (h : IsFinalEncounter w p q z) : z.finalDegree = q := by
  rcases z with ⟨_ | ⟨e, l⟩, ρ, hm, hmono⟩
  · exact h.elim
  · simpa only [finalDegree_def, ← Fin.castSucc_zero, Fin.snoc_castSucc] using h.2.1

/-- If the backward line from `Q` in the direction of `q ≠ 0` meets no wall support
at a signed transverse encounter, no ray has final degree `q`, so the component of
the full weighted evaluation vanishes. -/
theorem decompose_cutoffDecoratedEvaluation_eq_zero_of_forall_not_encounter
    [Finite J] (hq0 : q ≠ 0)
    (hnone : ∀ e (u : ℝ), 0 < u → f e (v q) ≠ 0 → SignType.sign (f e (v q)) = ε e →
      f e (Q + u • v q) = c e → Q + u • v q ∈ P e → False) :
    (DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) = 0 := by
  have hempty : IsEmpty
      {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q} := by
    refine ⟨fun ⟨z, hz⟩ => ?_⟩
    rcases z with ⟨_ | ⟨e, l⟩, ρ, hm, hmono⟩
    · exact hq0 (by simpa only [finalDegree_def, Fin.snoc_zero] using hz.symm)
    · obtain ⟨htrans, τ, hτ, -, hheight, hmem, -⟩ := ρ.2.exists_finalEncounter
      have hdeg : Fin.snoc (α := fun _ => Γ) ρ.1.val 0 0 = q := by
        simpa only [finalDegree_def] using hz
      have hq' : ρ.1.val 0 = q := by
        simpa only [← Fin.castSucc_zero, Fin.snoc_castSucc] using hdeg
      rw [hdeg] at htrans hheight hmem
      exact hnone e τ hτ htrans (by simpa only [hq', List.get_cons_zero] using ρ.crossing_sign 0)
        hheight hmem
  rw [decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree]
  simp

open Classical in
/-- Let the backward line from `Q` in the direction of the final degree `q ≠ 0`
meet a wall support first at the regular encounter `w`, at ray parameter `t`. For all
sufficiently short incoming displacements, the degree-`q` component of the full
weighted evaluation at `Q` is the sum, over the adjacent degrees `p` preserving
the normal velocity at `w`, of the degree-`q` component of `T w` applied to the
degree-`p` evaluation at the incoming germ `Q + t • v q + η • v p`. The degree
`p = q` of an unchanged coefficient is included. -/
theorem eventually_decompose_cutoffDecoratedEvaluation_eq_sum_finalEncounter
    [Finite J] [Finite K] (hq : q ∈ d.cutoff k) (hq0 : q ≠ 0)
    (hP : ∀ j, P j ⊆ ⋃ b, W b) (ht : 0 < t)
    (htrans : f w (v q) ≠ 0) (hsign : SignType.sign (f w (v q)) = ε w)
    (hheight : f w (Q + t • v q) = c w) (hinc : Q + t • v q ∈ P w)
    (hunique : ∀ e, f e (v q) ≠ 0 → SignType.sign (f e (v q)) = ε e →
      f e (Q + t • v q) = c e → Q + t • v q ∈ P e → e = w)
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + t • v q ∈ W j → ∀ y ∈ W j, f w y = c w)
    (hclosedS : ∀ j, IsClosed (S j)) (hregular : ∀ j, Q + t • v q ∉ S j)
    (hW : ∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ W j)
    (hS : ∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ S j) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      (DirectSum.decompose ℳ
        (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) =
        ∑ p ∈ (d.finite_cutoff k).toFinset with
            q - p ∈ d.monoid ∧ f w (v q) = f w (v p),
          (DirectSum.decompose ℳ (T w (DirectSum.decompose ℳ
            (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
              (Q + t • v q + η • v p)) p)) q : M) := by
  classical
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  set Ps := (d.finite_cutoff k).toFinset.filter
    (fun p => q - p ∈ d.monoid ∧ f w (v q) = f w (v p)) with hPs
  have hevent : ∀ p ∈ Ps, ∀ᶠ η : ℝ in 𝓝[>] 0,
      (∑ z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
        if IsFinalEncounter w p q z then z.decoration else 0) =
        (DirectSum.decompose ℳ (T w (DirectSum.decompose ℳ
          (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
            (Q + t • v q + η • v p)) p)) q : M) := by
    intro p hp
    obtain ⟨hpc, hqp, hn⟩ := Finset.mem_filter.mp hp
    exact eventually_sum_finalEncounter_eq_component w p q k
      (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp hpc)).2 hq hqp t ht hn htrans hsign
      hheight hinc hclosedW hplane hclosedS hregular hW hS
  have hsplit : (DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) =
      ∑ p ∈ Ps, ∑ z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
        if IsFinalEncounter w p q z then z.decoration else 0 := by
    rw [Finset.sum_comm, decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree,
      ← Finset.sum_subtype (Finset.univ.filter fun z => z.finalDegree = q) (by simp),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z.finalDegree = q
    · obtain ⟨p, hp, hpc, hqp, hn⟩ :=
        exists_isFinalEncounter w q t hq hq0 hP ht hinc hW hunique z hz
      rw [ite_eq_left hz, Finset.sum_eq_single p]
      · rw [ite_eq_left hp]
      · intro p' _ hne
        exact ite_eq_right fun h => hne (hp.unique w q h).symm
      · intro hnot
        exact (hnot (by simp [hPs, hpc, hqp, hn, (d.finite_cutoff k).mem_toFinset])).elim
    · rw [ite_eq_right hz]
      exact (Finset.sum_eq_zero fun p _ => ite_eq_right fun h => hz h.finalDegree_eq).symm
  filter_upwards [(Filter.eventually_all_finset Ps).mpr hevent] with η hη
  rw [hsplit]
  exact Finset.sum_congr rfl hη

end Decomposition

end Mei.CutoffDecoratedRay
