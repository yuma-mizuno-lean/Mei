/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.LinearAlgebra.GradedModule.History.Uniform

/-!
# Uniform geometric expansions of decorated rays

For a fixed signed encounter itinerary, uniform finite history support on a
linear incoming family gives a finite sum of linear maps computing its actual
weighted ray evaluation. Each summand retains its normal-velocity and sign tests,
selected support incidences, wall and singular avoidance, and full incoming tail.
The same sum works for every input, even when specialization kills decorations.
Finite generation of the incoming range supplies the required support.

For rational polyhedral data this yields a finite partition of endpoint space
into relative interiors of closed polyhedra carrying fixed linear maps. The
partition works simultaneously for all incoming parameters, without a positive
group grading or a cutoff on degrees. It supplies uniform geometric branch totals
for comparing local resolutions; it does not assert identities between resolutions
or admissibility of boundary paths.

The coefficient expansion is the shared `sum_ite_homogeneousHistory_comp_apply`.
The geometric interpretation follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4), and
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M E Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid E] [Module R E] [DecidableEq Γ]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : Fin n → Module.End R M) (p₀ : Γ) (α : E →ₗ[R] ℳ p₀)
  (v : Γ → V) (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (ε : Fin n → SignType) (P : Fin n → Set V) (W : J → Set V) (S : K → Set V)
  (C : Set V)

local notation "input" => LinearMap.comp (Submodule.subtype (ℳ p₀)) α
local notation "H(" p ")" => LinearMap.comp (homogeneousHistory ℳ T p) input

open Classical in
/-- Uniformly supported histories compute actual ray evaluations as a sum of
linear maps selected by the full geometric domain. The support is chosen before
the endpoint or the incoming parameter; zero terms remain in this operator sum. -/
theorem decoratedRayEvaluation_eq_uniform_sum
    (s : Finset (Fin n → Γ)) (hs : ∀ p ∉ s, H(p) = 0) (Q : V) (x : E) :
    decoratedRayEvaluation ℳ T p₀ (α x) v f c ε P W S C Q =
      (∑ p ∈ s, if (∀ j, f j (v (p j)) =
          f j (v (Fin.snoc (α := fun _ => Γ) p p₀ j.succ)) ∧
            SignType.sign (f j (v (p j))) = ε j) ∧
          Q ∈ admissibleBackwardDomain f c
            (fun j => v (Fin.snoc (α := fun _ => Γ) p p₀ j)) P W S C
        then H(p) else 0) x := by
  have he := sum_ite_homogeneousHistory_comp_apply ℳ T input s hs
    (fun p => (∀ j, f j (v (p j)) =
      f j (v (Fin.snoc (α := fun _ => Γ) p p₀ j.succ)) ∧
        SignType.sign (f j (v (p j))) = ε j) ∧
      Q ∈ admissibleBackwardDomain f c
        (fun j => v (Fin.snoc (α := fun _ => Γ) p p₀ j)) P W S C) x
  rw [decoratedRayEvaluation_eq_sum_homogeneousHistory]
  -- The expanded conjunction and the abstract predicate choose different
  -- decidability instances; compare their conditional summands explicitly.
  convert he.symm using 1
  · apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> rfl
  · apply congrArg (fun L : E →ₗ[R] M => L x)
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> rfl

open Classical in
/-- A finitely generated incoming range admits one finite geometric history
expansion for every endpoint and every input. No finiteness of the grading or
of its homogeneous pieces is required. -/
theorem exists_uniform_decoratedRayEvaluation_expansion
    (hα : (LinearMap.range α).FG) :
    ∃ s : Finset (Fin n → Γ), (∀ p ∉ s, H(p) = 0) ∧ ∀ Q x,
      decoratedRayEvaluation ℳ T p₀ (α x) v f c ε P W S C Q =
        (∑ p ∈ s, if (∀ j, f j (v (p j)) =
            f j (v (Fin.snoc (α := fun _ => Γ) p p₀ j.succ)) ∧
              SignType.sign (f j (v (p j))) = ε j) ∧
            Q ∈ admissibleBackwardDomain f c
              (fun j => v (Fin.snoc (α := fun _ => Γ) p p₀ j)) P W S C
          then H(p) else 0) x := by
  have hinput : (LinearMap.range input).FG := by
    rw [LinearMap.range_comp]
    exact hα.map _
  obtain ⟨s, hs⟩ := exists_uniform_homogeneousHistory_support ℳ T input hinput
  exact ⟨s, hs, decoratedRayEvaluation_eq_uniform_sum ℳ T p₀ α v f c ε P W S C s hs⟩

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ) [Finite J] [Finite K]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q => i (w q)

include hf hP hW hS hC in
open Classical in
/-- One closed polyhedral partition computes a uniformly supported linear
family of actual ray sums at every endpoint, including lower-dimensional strata.
The maps retain whole decorations and can have zero or cancelling terms. -/
theorem exists_decoratedRayEvaluation_uniform_partition
    (s : Finset (Fin n → Γ)) (hs : ∀ p ∉ s, H(p) = 0) :
    ∃ (m : ℕ) (B : Fin m → Set V) (L : Fin m → E →ₗ[R] M),
      (∀ j, (B j).Nonempty ∧ IsRationalNormalPolyhedron h (B j) ∧
        (intrinsicInterior ℝ (B j)).Nonempty) ∧
      (Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B j))
        (intrinsicInterior ℝ (B l))) ∧
      (⋃ j, intrinsicInterior ℝ (B j)) = Set.univ ∧
      ∀ j Q, Q ∈ intrinsicInterior ℝ (B j) → ∀ x,
        decoratedRayEvaluation ℳ T p₀ (α x) vel f c ε P W S C Q = L j x := by
  classical
  let N (p : Fin n → Γ) : Prop := ∀ j, f j (i (w (p j))) =
    f j (i (w (Fin.snoc (α := fun _ => Γ) p p₀ j.succ))) ∧
      SignType.sign (f j (i (w (p j)))) = ε j
  let D (p : Fin n → Γ) : Set V := {Q | N p ∧ Q ∈ admissibleBackwardDomain f c
    (fun j => i (w (Fin.snoc (α := fun _ => Γ) p p₀ j))) P W S C}
  have hD (p : Fin n → Γ) : IsRationalSemilinear h (D p) := by
    by_cases hp : N p
    · have he : D p = admissibleBackwardDomain f c
          (fun j => i (w (Fin.snoc (α := fun _ => Γ) p p₀ j))) P W S C := by
        ext Q
        exact and_iff_right hp
      rw [he]
      exact isRationalSemilinear_admissibleBackwardDomain f c P W S C
        (fun j => w (Fin.snoc (α := fun _ => Γ) p p₀ j)) hf hP hW hS hC
    · have he : D p = ∅ := by
        ext Q
        simp only [D, mem_ofPred_eq, hp, false_and, mem_empty_iff_false]
      rw [he]
      exact IsRationalSemilinear.empty h
  obtain ⟨m, B, L, hB, hdisj, hcover, hval⟩ :=
    IsRationalSemilinear.exists_common_weighted_polyhedralPartition
      (fun _ : Unit => (s : Type _)) (fun _ p => D p.val)
      (fun _ p => hD p.val) (fun _ p => H(p.val))
  refine ⟨m, B, fun j => L j (), hB, hdisj, hcover, fun j Q hQ x => ?_⟩
  rw [decoratedRayEvaluation_eq_uniform_sum ℳ T p₀ α vel f c ε P W S C s hs]
  have he := hval j () Q hQ
  have hsum := Finset.sum_coe_sort s
    (fun p => if Q ∈ D p then H(p) else 0)
  have he' : (∑ p ∈ s, if Q ∈ D p then H(p) else 0) = L j () := by
    calc
      _ = ∑ p : (s : Type _), if Q ∈ D p.val then H(p.val) else 0 := hsum.symm
      _ = L j () := by
        -- Normalize the decidability instance of the geometric membership test.
        convert he using 1
        apply Finset.sum_congr rfl
        intro p _
        split_ifs <;> rfl
  convert LinearMap.congr_fun he' x using 1

include hf hP hW hS hC in
/-- Finite generation of the incoming range supplies an input-independent
polyhedral partition for the actual weighted evaluations. This applies to every
finite list of test inputs and all of their linear combinations. -/
theorem exists_decoratedRayEvaluation_uniform_partition_of_fg
    (hα : (LinearMap.range α).FG) :
    ∃ (m : ℕ) (B : Fin m → Set V) (L : Fin m → E →ₗ[R] M),
      (∀ j, (B j).Nonempty ∧ IsRationalNormalPolyhedron h (B j) ∧
        (intrinsicInterior ℝ (B j)).Nonempty) ∧
      (Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B j))
        (intrinsicInterior ℝ (B l))) ∧
      (⋃ j, intrinsicInterior ℝ (B j)) = Set.univ ∧
      ∀ j Q, Q ∈ intrinsicInterior ℝ (B j) → ∀ x,
        decoratedRayEvaluation ℳ T p₀ (α x) vel f c ε P W S C Q = L j x := by
  obtain ⟨s, hs, -⟩ := exists_uniform_decoratedRayEvaluation_expansion
    ℳ T p₀ α vel f c ε P W S C hα
  exact exists_decoratedRayEvaluation_uniform_partition
    ℳ T p₀ α f c ε P W S C h w hf hP hW hS hC s hs

end Rational

end Mei
