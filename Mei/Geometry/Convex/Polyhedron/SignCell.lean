/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-!
# Sign cells of affine arrangements

An affine family partitions the ambient space by the signs of its values.
The closure of a nonempty sign cell is obtained by weakening its strict
inequalities, while retaining its equality rows. Nonemptiness is essential:
an inconsistent strict system can have a nonempty weakened system.
-/

public section

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The locus realizing an assigned sign for each affine row. -/
@[expose] def signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) : Set V :=
  {x | ∀ j, SignType.sign (g j x) = σ j}

/-- The weak sign conditions, with equality rows retained exactly. -/
@[expose] def weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) : Set V :=
  {x | ∀ j, match σ j with
    | .zero => g j x = 0
    | .neg => g j x ≤ 0
    | .pos => 0 ≤ g j x}

/-- Strict sign conditions imply their weak versions. -/
theorem signCell_subset_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    signCell g σ ⊆ weakSignCell g σ := by
  intro x hx j
  have hj := hx j
  cases h : σ j with
  | zero => exact sign_eq_zero_iff.mp (by simpa [h] using hj)
  | neg => exact (sign_eq_neg_one_iff.mp (by simpa [h] using hj)).le
  | pos => exact (sign_eq_one_iff.mp (by simpa [h] using hj)).le

/-- The weak sign cell is closed, including for an infinite family. -/
theorem isClosed_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    IsClosed (weakSignCell g σ) := by
  have he : weakSignCell g σ = ⋂ j, {x : V | match σ j with
      | .zero => g j x = 0 | .neg => g j x ≤ 0 | .pos => 0 ≤ g j x} := by
    ext x
    simp [weakSignCell]
  rw [he]
  apply isClosed_iInter
  intro j
  cases σ j
  · exact isClosed_eq (g j).continuous continuous_const
  · exact isClosed_le (g j).continuous continuous_const
  · exact isClosed_le continuous_const (g j).continuous

/-- Moving from a weak solution towards a strict solution makes every prescribed
nonzero sign strict while retaining all equality rows. -/
theorem openSegment_subset_signCell {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    {x p : V} (hx : x ∈ weakSignCell g σ) (hp : p ∈ signCell g σ) :
    openSegment ℝ x p ⊆ signCell g σ := by
  rintro y ⟨a, b, ha, hb, hab, rfl⟩ j
  have he : g j (a • x + b • p) = a * g j x + b * g j p :=
    Convex.combo_affine_apply (f := (g j).toAffineMap) hab
  have hxj := hx j
  have hpj := hp j
  rw [he]
  cases h : σ j with
  | zero =>
    have hpx : g j p = 0 := sign_eq_zero_iff.mp (by simpa [h] using hpj)
    simp only [h] at hxj
    simp [hxj, hpx]
  | neg =>
    apply sign_eq_neg_one_iff.mpr
    have hpp : g j p < 0 := sign_eq_neg_one_iff.mp (by simpa [h] using hpj)
    simp only [h] at hxj
    exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le hxj)
      (mul_neg_of_pos_of_neg hb hpp)
  | pos =>
    apply sign_eq_one_iff.mpr
    have hpp : 0 < g j p := sign_eq_one_iff.mp (by simpa [h] using hpj)
    simp only [h] at hxj
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le hxj) (mul_pos hb hpp)

/-- For a nonempty sign cell, closure is exactly the weakened system. -/
theorem closure_signCell {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    (hne : (signCell g σ).Nonempty) : closure (signCell g σ) = weakSignCell g σ := by
  apply Set.Subset.antisymm
  · exact closure_minimal (signCell_subset_weakSignCell g σ) (isClosed_weakSignCell g σ)
  · obtain ⟨p, hp⟩ := hne
    intro x hx
    exact closure_mono (openSegment_subset_signCell hx hp)
      (segment_subset_closure_openSegment (left_mem_segment ℝ x p))

/-- Every point belongs to the cell recording its actual affine signs. -/
theorem mem_signCell_sign (g : ι → (V →ᴬ[ℝ] ℝ)) (x : V) :
    x ∈ signCell g (fun j => SignType.sign (g j x)) := fun _ => rfl

/-- A point cannot belong to two cells with distinct sign assignments. -/
theorem signCell_disjoint {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType} (h : σ ≠ τ) :
    Disjoint (signCell g σ) (signCell g τ) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact h (funext fun j => (hx j).symm.trans (hy j))

/-- Sign cells cover the entire ambient space. -/
theorem iUnion_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) : ⋃ σ, signCell g σ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨_, mem_signCell_sign g x⟩

/-- Each strict sign cell is convex, for an arbitrary family of affine rows. -/
theorem convex_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    _root_.Convex ℝ (signCell g σ) := by
  have he : signCell g σ = ⋂ j, {x : V | SignType.sign (g j x) = σ j} := by
    ext x
    simp [signCell]
  rw [he]
  apply convex_iInter
  intro j
  cases σ j with
  | zero =>
    have he : {x : V | SignType.sign (g j x) = .zero} = (g j) ⁻¹' {0} := by
      ext x
      simp
    rw [he]
    exact _root_.Convex.affine_preimage (g j).toAffineMap (convex_singleton 0)
  | neg =>
    have he : {x : V | SignType.sign (g j x) = .neg} = (g j) ⁻¹' Set.Iio 0 := by
      ext x
      simp [sign_eq_neg_one_iff]
    rw [he]
    exact _root_.Convex.affine_preimage (g j).toAffineMap (convex_Iio 0)
  | pos =>
    have he : {x : V | SignType.sign (g j x) = .pos} = (g j) ⁻¹' Set.Ioi 0 := by
      ext x
      simp [sign_eq_one_iff]
    rw [he]
    exact _root_.Convex.affine_preimage (g j).toAffineMap (convex_Ioi 0)

/-- Weak sign cells are convex, including for infinite families and empty strict cells. -/
theorem convex_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    _root_.Convex ℝ (weakSignCell g σ) := by
  intro x hx y hy a b ha hb hab j
  have he : g j (a • x + b • y) = a * g j x + b * g j y :=
    Convex.combo_affine_apply (f := (g j).toAffineMap) hab
  have hxj := hx j
  have hyj := hy j
  rw [he]
  cases h : σ j with
  | zero =>
    simp only [h] at hxj hyj
    simp [hxj, hyj]
  | neg =>
    simp only [h] at hxj hyj
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hxj)
      (mul_nonpos_of_nonneg_of_nonpos hb hyj)
  | pos =>
    simp only [h] at hxj hyj
    exact add_nonneg (mul_nonneg ha hxj) (mul_nonneg hb hyj)

/-- A sign assignment specializes another by replacing some of its signs with zero. -/
def SignSpecializes (τ σ : ι → SignType) : Prop := ∀ j, τ j = 0 ∨ τ j = σ j

/-- Weak sign conditions say exactly that the actual signs specialize the prescribed signs. -/
theorem mem_weakSignCell_iff_specializes {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    {x : V} : x ∈ weakSignCell g σ ↔ SignSpecializes (fun j => SignType.sign (g j x)) σ := by
  apply forall_congr'
  intro j
  cases σ j with
  | zero => simp [sign_eq_zero_iff]
  | neg =>
    simp only [SignType.neg_eq_neg_one, sign_eq_zero_iff, sign_eq_neg_one_iff]
    exact le_iff_eq_or_lt
  | pos =>
    simp only [SignType.pos_eq_one, sign_eq_zero_iff, sign_eq_one_iff]
    exact le_iff_eq_or_lt'

/-- A weak sign cell is the disjoint union of the strict cells obtained by zero specialization. -/
theorem weakSignCell_eq_iUnion_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    weakSignCell g σ = ⋃ τ : {τ // SignSpecializes τ σ}, signCell g τ.val := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr
      ⟨⟨fun j => SignType.sign (g j x), mem_weakSignCell_iff_specializes.mp hx⟩,
        mem_signCell_sign g x⟩
  · intro hx
    obtain ⟨τ, hxτ⟩ := Set.mem_iUnion.mp hx
    apply mem_weakSignCell_iff_specializes.mpr
    intro j
    change SignType.sign (g j x) = 0 ∨ SignType.sign (g j x) = σ j
    rw [hxτ j]
    exact τ.property j

/-- Replacing more signs by zero restricts the corresponding weak sign cell. -/
theorem weakSignCell_subset_of_specializes {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType}
    (h : SignSpecializes τ σ) : weakSignCell g τ ⊆ weakSignCell g σ := by
  intro x hx
  apply mem_weakSignCell_iff_specializes.mpr
  have hτ := mem_weakSignCell_iff_specializes.mp hx
  intro j
  rcases hτ j with hz | ht
  · exact Or.inl hz
  · rcases h j with hz | hs
    · exact Or.inl (ht.trans hz)
    · exact Or.inr (ht.trans hs)

/-- Finitely many affine rows give polyhedral weak sign cells; equality rows are
encoded by two opposite affine inequalities. -/
theorem isConvexPolyhedron_weakSignCell [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (σ : ι → SignType) : TauCeti.IsConvexPolyhedron (weakSignCell g σ) := by
  let rows : ι × Bool → (V →ᴬ[ℝ] ℝ) := fun p => match σ p.1 with
    | .zero => if p.2 then g p.1 else -g p.1
    | .neg => g p.1
    | .pos => -g p.1
  have he : weakSignCell g σ = {x : V | ∀ p, rows p x ≤ 0} := by
    ext x
    constructor
    · intro hx ⟨j, b⟩
      have hxj := hx j
      cases h : σ j <;> cases b <;> simp_all [rows]
    · intro hx j
      have h₁ := hx (j, true)
      have h₂ := hx (j, false)
      cases h : σ j with
      | zero =>
        simp only [rows, h, Bool.false_eq_true, ↓reduceIte, ContinuousAffineMap.neg_apply,
          neg_nonpos] at h₁ h₂
        exact le_antisymm h₁ h₂
      | neg => simpa [rows, h] using h₁
      | pos => simpa [rows, h] using h₁
  rw [he]
  exact TauCeti.isConvexPolyhedron_setOf_forall rows

/-- The closures of realized cells of a finite arrangement are convex polyhedra. -/
theorem isConvexPolyhedron_closure_signCell [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ : ι → SignType} (hne : (signCell g σ).Nonempty) :
    TauCeti.IsConvexPolyhedron (closure (signCell g σ)) := by
  rw [closure_signCell hne]
  exact isConvexPolyhedron_weakSignCell g σ

/-- A finite affine family has only finitely many sign cells. Empty labels are permitted. -/
theorem finite_range_signCell [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) :
    (Set.range (signCell g)).Finite := Set.finite_range _

/-- The sign-cell partition has pairwise disjoint cells. -/
theorem pairwiseDisjoint_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) :
    Set.PairwiseDisjoint (Set.univ : Set (ι → SignType)) (signCell g) := by
  intro σ _ τ _ h
  exact signCell_disjoint h

/-- A zero-specialized weak sign cell is an extreme subset of the original weak
cell. The specialized cell is allowed to be empty. -/
theorem isExtreme_weakSignCell_of_specializes {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ τ : ι → SignType} (h : SignSpecializes τ σ) :
    IsExtreme ℝ (weakSignCell g σ) (weakSignCell g τ) := by
  refine ⟨weakSignCell_subset_of_specializes h, ?_⟩
  intro x hx y hy z hz hzxy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzxy
  intro j
  rcases h j with hj | hj
  · rw [hj]
    have hzj := hz j
    simp only [hj] at hzj
    have he : a * g j x + b * g j y = 0 := by
      have hcombo : g j (a • x + b • y) = a * g j x + b * g j y :=
        Convex.combo_affine_apply (f := (g j).toAffineMap) hab
      rwa [hcombo] at hzj
    have hxj := hx j
    have hyj := hy j
    cases hs : σ j with
    | zero => simpa only [hs] using hxj
    | neg =>
      simp only [hs] at hxj hyj
      have hax := mul_nonpos_of_nonneg_of_nonpos ha.le hxj
      have hby := mul_nonpos_of_nonneg_of_nonpos hb.le hyj
      have haz : a * g j x = 0 := by linarith
      exact (mul_eq_zero.mp haz).resolve_left ha.ne'
    | pos =>
      simp only [hs] at hxj hyj
      have hax := mul_nonneg ha.le hxj
      have hby := mul_nonneg hb.le hyj
      exact (mul_eq_zero.mp ((add_eq_zero_iff_of_nonneg hax hby).mp he).1).resolve_left ha.ne'
  · simpa only [hj] using hx j

/-- The common zero specialization keeps exactly the signs on which two assignments agree. -/
def commonSignPattern (σ τ : ι → SignType) : ι → SignType :=
  fun j => if σ j = τ j then σ j else 0

/-- Intersecting two weak sign cells forces every disagreement row to zero. -/
theorem weakSignCell_inter (g : ι → (V →ᴬ[ℝ] ℝ)) (σ τ : ι → SignType) :
    weakSignCell g σ ∩ weakSignCell g τ = weakSignCell g (commonSignPattern σ τ) := by
  ext x
  constructor
  · intro hx j
    by_cases heq : σ j = τ j
    · simpa only [commonSignPattern, ite_eq_left heq] using hx.1 j
    · simp only [commonSignPattern, ite_eq_right heq]
      have hxj := hx.1 j
      have hyj := hx.2 j
      cases hs : σ j <;> cases ht : τ j <;> simp_all <;> linarith
  · intro hx
    have hleft : SignSpecializes (commonSignPattern σ τ) σ := by
      intro j
      by_cases h : σ j = τ j <;> simp [commonSignPattern, h]
    have hright : SignSpecializes (commonSignPattern σ τ) τ := by
      intro j
      by_cases h : σ j = τ j <;> simp [commonSignPattern, h]
    exact ⟨weakSignCell_subset_of_specializes hleft hx,
      weakSignCell_subset_of_specializes hright hx⟩

/-- Every intersection of weak sign cells is an extreme subset of the first cell,
including when the intersection is empty. -/
theorem isExtreme_weakSignCell_inter (g : ι → (V →ᴬ[ℝ] ℝ)) (σ τ : ι → SignType) :
    IsExtreme ℝ (weakSignCell g σ) (weakSignCell g σ ∩ weakSignCell g τ) := by
  rw [weakSignCell_inter]
  apply isExtreme_weakSignCell_of_specializes
  intro j
  by_cases h : σ j = τ j <;> simp [commonSignPattern, h]

/-- The closure of a realized sign cell consists precisely of its strict zero-specializations. -/
theorem closure_signCell_eq_iUnion {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    (hne : (signCell g σ).Nonempty) :
    closure (signCell g σ) = ⋃ τ : {τ // SignSpecializes τ σ}, signCell g τ.val := by
  rw [closure_signCell hne, weakSignCell_eq_iUnion_signCell]

/-- Intersections of closures of realized cells are extreme subsets of each
closure. The intersection may be empty; interchange assignments for the symmetric statement. -/
theorem isExtreme_closure_signCell_inter {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType}
    (hσ : (signCell g σ).Nonempty) (hτ : (signCell g τ).Nonempty) :
    IsExtreme ℝ (closure (signCell g σ))
      (closure (signCell g σ) ∩ closure (signCell g τ)) := by
  rw [closure_signCell hσ, closure_signCell hτ]
  exact isExtreme_weakSignCell_inter g σ τ

/-- A finite affine family has finitely many distinct closed sign-cell supports. -/
theorem finite_range_closure_signCell [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) :
    (Set.range (fun σ => closure (signCell g σ))).Finite := Set.finite_range _

/-- Closed sign-cell supports cover the ambient space. Empty labels contribute nothing. -/
theorem iUnion_closure_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) :
    ⋃ σ, closure (signCell g σ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨_, subset_closure (mem_signCell_sign g x)⟩

/-- Combining affine families refines their strict cells by intersection. -/
theorem signCell_sum {κ : Type*} (g : ι → (V →ᴬ[ℝ] ℝ)) (h : κ → (V →ᴬ[ℝ] ℝ))
    (σ : ι → SignType) (τ : κ → SignType) :
    signCell (Sum.elim g h) (Sum.elim σ τ) = signCell g σ ∩ signCell h τ := by
  ext x
  simp [signCell, Sum.forall]

/-- Combining affine families refines their weak cells by intersection. -/
theorem weakSignCell_sum {κ : Type*} (g : ι → (V →ᴬ[ℝ] ℝ)) (h : κ → (V →ᴬ[ℝ] ℝ))
    (σ : ι → SignType) (τ : κ → SignType) :
    weakSignCell (Sum.elim g h) (Sum.elim σ τ) = weakSignCell g σ ∩ weakSignCell h τ := by
  ext x
  simp [weakSignCell, Sum.forall]

end Mei.Convex
