/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family

/-!
# Uniform linear expansions of varying-chamber ray evaluations

A finite encounter inventory and finite contributing history supports on an
incoming linear family give a sum of linear maps computing its actual ray
evaluation. The chamber modules and their degree types may differ. The geometric
selection retains every encounter, the normal and sign conditions, wall and
singular avoidance, and admission of the whole incoming tail to its source.
Zero terms remain in the linear-map sum even when an individual input kills a
decoration. Finite generation is required only of the incoming range to obtain
uniform supports automatically.

For rational polyhedral geometry, one partition of endpoint space into disjoint
relative interiors of closed polyhedra computes the evaluations of every incoming
parameter by fixed linear maps. This gives branch totals for local resolutions
without requiring globally finite gradings or finite-dimensional coefficients.
It does not assert equalities between different local resolutions.

The expansions use the shared `Quiver.Path` history API and the common weighted
polyhedral partition theorem. The interpretation follows Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3.2
(arXiv:1601.07081v4), and Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V J K E : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (s : Finset (Path a b))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "dirs(" p ", " d ")" => Path.Degrees.reverseVertexLabels v i₀ p d
local notation "normals(" p ")" => Path.reverseArrowLabels ν p
local notation "N(" p ", " d ")" => (fun j : Fin (Path.length p) =>
  normals(p) j (dirs(p, d) (Fin.castSucc j)) = normals(p) j (dirs(p, d) (Fin.succ j)) ∧
    SignType.sign (normals(p) j (dirs(p, d) (Fin.castSucc j))) = Path.reverseArrowLabels ε p j)
local notation "D(" p ", " d ")" => admissibleBackwardDomain normals(p)
  (Path.reverseArrowLabels c p) dirs(p, d) (Path.reverseArrowLabels P p) W S C

open Classical in
/-- Actual ray evaluation is the sum of whole histories selected by the complete
geometric conditions. Distinct histories with the same spatial path stay distinct. -/
theorem pathDecoratedEvaluation_eq_sum_homogeneousHistory (x : ℳ a i₀) (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X =
      ∑ p : (s : Type _), ∑ d ∈ p.val.historySupport T ℳ (x : M a),
        if (∀ j, N(p.val, d) j) ∧ X ∈ D(p.val, d)
        then p.val.homogeneousHistory T ℳ d x else 0 := by
  classical
  let : ∀ p : (s : Type _),
      Fintype (PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p.val X) :=
    fun _ => Fintype.ofFinite _
  let := Fintype.ofFinite (Σ p : (s : Type _),
    PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p.val X)
  rw [pathDecoratedEvaluation_def]
  dsimp only
  trans ∑ p : (s : Type _),
    ∑ r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p.val X, r.decoration
  · -- The evaluation uses `Fintype.ofFinite`, while the iterated sum uses the
    -- dependent-sum instance. Both enumerate the same finite type.
    convert Fintype.sum_sigma (fun r : Σ p : (s : Type _),
      PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p.val X => r.2.decoration) using 1
    congr 1
    ext r
    simp
  apply Finset.sum_congr rfl
  intro p _
  rw [sum_pathDecoratedRay_eq_sum_histories]
  trans ∑ d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p.val,
    if X ∈ D(p.val, d) then p.val.homogeneousHistory T ℳ d x else 0
  · exact Finset.sum_coe_sort (pathDecoratedHistorySupport T ℳ i₀ x v ν ε p.val)
      (fun d => if X ∈ D(p.val, d) then p.val.homogeneousHistory T ℳ d x else 0)
  · have hs : pathDecoratedHistorySupport T ℳ i₀ x v ν ε p.val =
        (p.val.historySupport T ℳ (x : M a)).filter (fun d => ∀ j, N(p.val, d) j) := by
      ext d
      simp only [mem_pathDecoratedHistorySupport, Finset.mem_filter, Path.mem_historySupport]
    rw [hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    exact (ite_and _ _ _ _).symm

variable [AddCommMonoid E] [Module R E] (α : E →ₗ[R] ℳ a i₀)

local notation "input" => LinearMap.comp (Submodule.subtype (ℳ a i₀)) α
local notation "H(" p ", " d ")" => LinearMap.comp (Path.homogeneousHistory T ℳ p d) input

open Classical in
/-- A uniform history support gives a geometric sum of linear maps for every
endpoint and input. The support is imposed before selecting geometric domains. -/
theorem pathDecoratedEvaluation_eq_uniform_sum
    (A : ∀ p : (s : Type _), Finset (p.val.Degrees ι))
    (hA : ∀ p d, d ∉ A p → H(p.val, d) = 0) (X : V) (x : E) :
    pathDecoratedEvaluation T ℳ i₀ (α x) s v ν ε c P W S C X =
      (∑ p : (s : Type _), ∑ d ∈ A p,
        if (∀ j, N(p.val, d) j) ∧ X ∈ D(p.val, d) then H(p.val, d) else 0) x := by
  rw [pathDecoratedEvaluation_eq_sum_homogeneousHistory]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  -- The abstract predicate and its expanded conjunction choose different
  -- decidability instances; compare their conditional summands explicitly.
  convert (p.val.sum_ite_homogeneousHistory_comp_apply T ℳ input (A p) (hA p)
    (fun d => (∀ j, N(p.val, d) j) ∧ X ∈ D(p.val, d)) x).symm using 1
  · apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  · simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl

open Classical in
/-- Finite generation of the incoming range supplies one finite complete-history
inventory for all endpoints and all inputs, including cancelling combinations. -/
theorem exists_uniform_pathDecoratedEvaluation_expansion (hα : (LinearMap.range α).FG) :
    ∃ A : ∀ p : (s : Type _), Finset (p.val.Degrees ι),
      (∀ p d, d ∉ A p → H(p.val, d) = 0) ∧ ∀ X x,
        pathDecoratedEvaluation T ℳ i₀ (α x) s v ν ε c P W S C X =
          (∑ p : (s : Type _), ∑ d ∈ A p,
            if (∀ j, N(p.val, d) j) ∧ X ∈ D(p.val, d) then H(p.val, d) else 0) x := by
  have hinput : (LinearMap.range input).FG := by
    rw [LinearMap.range_comp]
    exact hα.map _
  choose A hA using fun p : (s : Type _) => p.val.exists_uniform_historySupport T ℳ input hinput
  exact ⟨A, hA, pathDecoratedEvaluation_eq_uniform_sum T ℳ i₀ s v ν ε c P W S C α A hA⟩

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q d => i (w q d)
local notation "VD(" p ", " d ")" => admissibleBackwardDomain normals(p)
  (Path.reverseArrowLabels c p) (Path.Degrees.reverseVertexLabels vel i₀ p d)
  (Path.reverseArrowLabels P p) W S C
local notation "VN(" p ", " d ")" => (fun j : Fin (Path.length p) =>
  normals(p) j (Path.Degrees.reverseVertexLabels vel i₀ p d (Fin.castSucc j)) =
      normals(p) j (Path.Degrees.reverseVertexLabels vel i₀ p d (Fin.succ j)) ∧
    SignType.sign (normals(p) j (Path.Degrees.reverseVertexLabels vel i₀ p d (Fin.castSucc j))) =
      Path.reverseArrowLabels ε p j)

include hν hP hW hS hC in
open Classical in
/-- One partition of the entire endpoint space computes all inputs by fixed
linear maps. Lower-dimensional strata, zero decorations and cancellations are
included; boundary paths need not themselves be admissible. -/
theorem exists_pathDecoratedEvaluation_uniform_partition
    (A : ∀ p : (s : Type _), Finset (p.val.Degrees ι))
    (hA : ∀ p d, d ∉ A p → H(p.val, d) = 0) :
    ∃ (n : ℕ) (B : Fin n → Set V) (L : Fin n → E →ₗ[R] M b),
      (∀ j, (B j).Nonempty ∧ IsRationalNormalPolyhedron h (B j) ∧
        (intrinsicInterior ℝ (B j)).Nonempty) ∧
      (Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B j))
        (intrinsicInterior ℝ (B l))) ∧
      (⋃ j, intrinsicInterior ℝ (B j)) = Set.univ ∧
      ∀ j X, X ∈ intrinsicInterior ℝ (B j) → ∀ x,
        pathDecoratedEvaluation T ℳ i₀ (α x) s vel ν ε c P W S C X = L j x := by
  let Labels := Σ p : (s : Type _), (A p : Type _)
  let domains (t : Labels) : Set V := {X | (∀ j, VN(t.1.val, t.2.val) j) ∧ X ∈ VD(t.1.val, t.2.val)}
  have hdomains (t : Labels) : IsRationalSemilinear h (domains t) := by
    by_cases ht : ∀ j, VN(t.1.val, t.2.val) j
    · have he : domains t = VD(t.1.val, t.2.val) := by
        ext X
        exact and_iff_right ht
      rw [he]
      exact isRationalSemilinear_pathDecoratedDomain
        i₀ ν c P W S C h w hν hP hW hS hC t.1.val t.2.val
    · have he : domains t = ∅ := by ext X; simp [domains, ht]
      rw [he]
      exact IsRationalSemilinear.empty h
  obtain ⟨n, B, L, hB, hdisj, hcover, hval⟩ :=
    IsRationalSemilinear.exists_common_weighted_polyhedralPartition
      (fun _ : Unit => Labels) (fun _ => domains) (fun _ => hdomains)
      (fun _ t => H(t.1.val, t.2.val))
  refine ⟨n, B, fun j => L j (), hB, hdisj, hcover, fun j X hX x => ?_⟩
  rw [pathDecoratedEvaluation_eq_uniform_sum T ℳ i₀ s vel ν ε c P W S C α A hA]
  have he := hval j () X hX
  rw [Fintype.sum_sigma] at he
  have hsum : (∑ p : (s : Type _), ∑ d ∈ A p,
      if (∀ j, VN(p.val, d) j) ∧ X ∈ VD(p.val, d) then H(p.val, d) else 0) = L j () := by
    calc
      _ = ∑ p : (s : Type _), ∑ d : (A p : Type _),
          if X ∈ domains ⟨p, d⟩ then H(p.val, d.val) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        exact (Finset.sum_coe_sort (A p) _).symm
      _ = L j () := by
        -- Normalize the decidability instance of the geometric membership test.
        convert he using 1
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> rfl
  exact LinearMap.congr_fun hsum x

include hν hP hW hS hC in
/-- A finitely generated incoming range has a common polyhedral partition for
all of its actual varying-chamber ray evaluations. This includes every finite
list of test inputs and all their scalar combinations. -/
theorem exists_pathDecoratedEvaluation_uniform_partition_of_fg
    (hα : (LinearMap.range α).FG) :
    ∃ (n : ℕ) (B : Fin n → Set V) (L : Fin n → E →ₗ[R] M b),
      (∀ j, (B j).Nonempty ∧ IsRationalNormalPolyhedron h (B j) ∧
        (intrinsicInterior ℝ (B j)).Nonempty) ∧
      (Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B j))
        (intrinsicInterior ℝ (B l))) ∧
      (⋃ j, intrinsicInterior ℝ (B j)) = Set.univ ∧
      ∀ j X, X ∈ intrinsicInterior ℝ (B j) → ∀ x,
        pathDecoratedEvaluation T ℳ i₀ (α x) s vel ν ε c P W S C X = L j x := by
  obtain ⟨A, hA, -⟩ := exists_uniform_pathDecoratedEvaluation_expansion
    T ℳ i₀ s vel ν ε c P W S C α hα
  exact exists_pathDecoratedEvaluation_uniform_partition
    T ℳ i₀ s ν ε c P W S C α h w hν hP hW hS hC A hA

end Rational

end Mei
