/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.SignCell
public import Mei.Geometry.Convex.Polyhedron.Face

/-!
# Faces of affine arrangements

Every nonempty convex extreme subset of a weak cell of a finite affine
arrangement is the closure of a realized strict zero-specialization. Thus the
finite family of closures of realized sign cells is closed under nonempty
convex extreme subsets. These are statements about continuous real affine rows;
no rationality assumption or bundled polyhedral-complex structure is introduced.
-/

public section

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The affine inequalities presenting a weak sign cell. Equality rows are
doubled, while the other rows are signed to be nonpositive. -/
def weakSignCellRows (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    ι × Bool → (V →ᴬ[ℝ] ℝ) := fun p => match σ p.1 with
  | .zero => if p.2 then g p.1 else -g p.1
  | .neg => g p.1
  | .pos => -g p.1

/-- The signed row is the original affine map or its negative, according to the sign. -/
theorem weakSignCellRows_eq (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) (p : ι × Bool) :
    weakSignCellRows g σ p = match σ p.1 with
      | .zero => if p.2 then g p.1 else -g p.1
      | .neg => g p.1
      | .pos => -g p.1 := by rfl

/-- Signing and doubling do not change the zero locus of an original row. -/
@[simp]
theorem weakSignCellRows_eq_zero_iff {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    {j : ι} {b : Bool} {x : V} :
    weakSignCellRows g σ (j, b) x = 0 ↔ g j x = 0 := by
  cases h : σ j <;> cases b <;> simp [weakSignCellRows, h]

/-- The doubled signed rows present exactly the original weak sign cell. -/
theorem mem_weakSignCell_iff_rows {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {x : V} :
    x ∈ weakSignCell g σ ↔ ∀ p, weakSignCellRows g σ p x ≤ 0 := by
  constructor
  · intro hx ⟨j, b⟩
    have hxj := hx j
    cases h : σ j <;> cases b <;> simp_all [weakSignCellRows]
  · intro hx j
    have h₁ := hx (j, true)
    have h₂ := hx (j, false)
    cases h : σ j with
    | zero =>
      simp only [weakSignCellRows, h, Bool.false_eq_true, ↓reduceIte,
        ContinuousAffineMap.neg_apply, neg_nonpos] at h₁ h₂
      exact le_antisymm h₁ h₂
    | neg => simpa [weakSignCellRows, h] using h₁
    | pos => simpa [weakSignCellRows, h] using h₁

/-- The weak cell agrees as a carrier with the finite-inequality presentation. -/
theorem weakSignCell_eq_setOf_rows (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    weakSignCell g σ = {x | ∀ p, weakSignCellRows g σ p x ≤ 0} := by
  ext x
  exact mem_weakSignCell_iff_rows

end Mei.Convex

namespace IsExtreme

open Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]

/-- Every nonempty convex extreme subset of a weak arrangement cell is the
closure of a realized strict cell obtained by zero specialization. -/
theorem exists_zeroSpecialization_signCell {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ : ι → SignType} {F : Set V} (hF : IsExtreme ℝ (weakSignCell g σ) F)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ τ : ι → SignType, SignSpecializes τ σ ∧ (signCell g τ).Nonempty ∧
      F = closure (signCell g τ) := by
  have hrows : IsExtreme ℝ {x | ∀ p, weakSignCellRows g σ p x ≤ 0} F := by
    rwa [← weakSignCell_eq_setOf_rows]
  obtain ⟨I, hI⟩ := hrows.eq_setOf_active
    (fun j => (weakSignCellRows g σ j).toAffineMap) hconv hne
  obtain ⟨p, hp, hpoint⟩ := hconv.exists_mem_zero_iff_forall hne
    (fun j => (weakSignCellRows g σ j).toAffineMap)
    (fun j x hx => mem_weakSignCell_iff_rows.mp (hF.subset hx) j)
  let τ : ι → SignType := fun j => SignType.sign (g j p)
  have hτ : SignSpecializes τ σ := mem_weakSignCell_iff_specializes.mp (hF.subset hp)
  have hτne : (signCell g τ).Nonempty := ⟨p, mem_signCell_sign g p⟩
  refine ⟨τ, hτ, hτne, ?_⟩
  rw [closure_signCell hτne]
  apply Set.Subset.antisymm
  · intro x hx j
    by_cases hj : τ j = 0
    · rw [hj]
      have hpj : g j p = 0 := sign_eq_zero_iff.mp hj
      have hprow : weakSignCellRows g σ (j, true) p = 0 :=
        weakSignCellRows_eq_zero_iff.mpr hpj
      have hxrow := (hpoint (j, true)).mp hprow x hx
      exact weakSignCellRows_eq_zero_iff.mp hxrow
    · have heq : τ j = σ j := by
        have hgpne : g j p ≠ 0 := fun hz => hj (sign_eq_zero_iff.mpr hz)
        have hppj := hF.subset hp j
        cases hs : σ j with
        | zero =>
          simp only [hs] at hppj
          exact False.elim (hgpne hppj)
        | neg =>
          simp only [hs] at hppj
          exact sign_eq_neg_one_iff.mpr (lt_of_le_of_ne hppj hgpne)
        | pos =>
          simp only [hs] at hppj
          exact sign_eq_one_iff.mpr (lt_of_le_of_ne hppj hgpne.symm)
      simpa only [heq] using hF.subset hx j
  · intro x hx
    rw [hI]
    refine ⟨mem_weakSignCell_iff_rows.mp (weakSignCell_subset_of_specializes hτ hx), ?_⟩
    intro j hj
    have hpI := (hI ▸ hp).2 j hj
    have hpj : g j.1 p = 0 := weakSignCellRows_eq_zero_iff.mp hpI
    have hτj : τ j.1 = 0 := sign_eq_zero_iff.mpr hpj
    have hxj := hx j.1
    simp only [hτj] at hxj
    exact weakSignCellRows_eq_zero_iff.mpr hxj

/-- Nonempty faces of realized closed sign cells are themselves realized closed
sign cells, with a zero-specialized assignment. -/
theorem exists_zeroSpecialization_closure_signCell {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ : ι → SignType} {F : Set V} (hF : IsExtreme ℝ (closure (signCell g σ)) F)
    (hσ : (signCell g σ).Nonempty) (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ τ : ι → SignType, SignSpecializes τ σ ∧ (signCell g τ).Nonempty ∧
      F = closure (signCell g τ) := by
  rw [closure_signCell hσ] at hF
  exact hF.exists_zeroSpecialization_signCell hconv hne

end IsExtreme

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual closed supports of the realized sign cells of an affine family. -/
def realizedSignCellClosures (g : ι → (V →ᴬ[ℝ] ℝ)) : Set (Set V) :=
  {P | ∃ σ, (signCell g σ).Nonempty ∧ P = closure (signCell g σ)}

/-- Membership means being the closure of a realized strict sign cell. -/
@[simp]
theorem mem_realizedSignCellClosures {g : ι → (V →ᴬ[ℝ] ℝ)} {P : Set V} :
    P ∈ realizedSignCellClosures g ↔
      ∃ σ, (signCell g σ).Nonempty ∧ P = closure (signCell g σ) := by
  simp only [realizedSignCellClosures, Set.mem_ofPred_eq]

/-- A member of the realized closure family has nonempty carrier. -/
theorem nonempty_of_mem_realizedSignCellClosures {g : ι → (V →ᴬ[ℝ] ℝ)} {P : Set V}
    (hP : P ∈ realizedSignCellClosures g) : P.Nonempty := by
  obtain ⟨σ, ⟨p, hp⟩, rfl⟩ := hP
  exact ⟨p, subset_closure hp⟩

/-- A finite arrangement has only finitely many realized closed sign-cell supports. -/
theorem finite_realizedSignCellClosures [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) :
    (realizedSignCellClosures g).Finite :=
  (finite_range_closure_signCell g).subset fun _ ⟨σ, _, heq⟩ => ⟨σ, heq.symm⟩

/-- The realized closed sign cells cover the ambient space. -/
theorem sUnion_realizedSignCellClosures (g : ι → (V →ᴬ[ℝ] ℝ)) :
    ⋃₀ realizedSignCellClosures g = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let σ := fun j => SignType.sign (g j x)
  have hx : x ∈ signCell g σ := mem_signCell_sign g x
  exact Set.mem_sUnion.mpr ⟨closure (signCell g σ), ⟨σ, ⟨x, hx⟩, rfl⟩, subset_closure hx⟩

/-- Every member of a finite realized closure family is a convex polyhedron. -/
theorem isConvexPolyhedron_of_mem_realizedSignCellClosures [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P : Set V} (hP : P ∈ realizedSignCellClosures g) :
    TauCeti.IsConvexPolyhedron P := by
  obtain ⟨σ, hσ, rfl⟩ := hP
  exact isConvexPolyhedron_closure_signCell hσ

/-- The full realized closure family is closed under all nonempty convex extreme subsets. -/
theorem _root_.IsExtreme.mem_realizedSignCellClosures [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P F : Set V} (hF : IsExtreme ℝ P F)
    (hP : P ∈ realizedSignCellClosures g) (hconv : Convex ℝ F) (hne : F.Nonempty) :
    F ∈ realizedSignCellClosures g := by
  obtain ⟨σ, hσ, rfl⟩ := hP
  obtain ⟨τ, _, hτ, heq⟩ := hF.exists_zeroSpecialization_closure_signCell hσ hconv hne
  exact ⟨τ, hτ, heq⟩

/-- Intersections of realized closed cells are extreme subsets of each cell;
the intersection is allowed to be empty. -/
theorem isExtreme_inter_of_mem_realizedSignCellClosures
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P Q : Set V}
    (hP : P ∈ realizedSignCellClosures g) (hQ : Q ∈ realizedSignCellClosures g) :
    IsExtreme ℝ P (P ∩ Q) := by
  obtain ⟨σ, hσ, rfl⟩ := hP
  obtain ⟨τ, hτ, rfl⟩ := hQ
  exact isExtreme_closure_signCell_inter hσ hτ

/-- Every nonempty intersection of two members of the finite realized closure
family is again a member of the same family. -/
theorem inter_mem_realizedSignCellClosures [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P Q : Set V}
    (hP : P ∈ realizedSignCellClosures g) (hQ : Q ∈ realizedSignCellClosures g)
    (hne : (P ∩ Q).Nonempty) : P ∩ Q ∈ realizedSignCellClosures g :=
  (isExtreme_inter_of_mem_realizedSignCellClosures hP hQ).mem_realizedSignCellClosures hP
    ((isConvexPolyhedron_of_mem_realizedSignCellClosures hP).convex.inter
      (isConvexPolyhedron_of_mem_realizedSignCellClosures hQ).convex) hne

end Mei.Convex
