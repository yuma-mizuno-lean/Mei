/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Basic
public import Mei.Algebra.DirectSum.Map
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Morphisms of homogeneous correspondences

A morphism of graded correspondences consists of three linear maps commuting with
the span legs and the admissible lifts. The two chamber maps carry homogeneous pieces
along specified degree maps. Identities, composition and reversal preserve these laws.

Transfers are natural under these morphisms: after regrading, all source output degrees
with the same image contribute to one target component. The sum is over the finite
homogeneous support of the lifted input. Injective degree maps give componentwise
naturality, in particular for comparisons preserving degrees such as truncations.

The component formulas use `DirectSum.decompose_map_eq_sum` and Tau Ceti's
`DirectSum.map_decompose_shift` for arbitrary and injective regradings, respectively.
No additive structure on the degree types is needed for these linear constructions.

The zero-extended lifts intertwine with a morphism on inputs whose homogeneous
support is admissible, and on the whole module when the degree map also preserves
inadmissible degrees.
-/

public section

namespace Mei.GradedCorrespondence

variable {R B U V B' U' V' B'' U'' V'' ι κ ι' κ' ι'' κ'' : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid V] [Module R V]
  [AddCommMonoid B'] [Module R B'] [AddCommMonoid U'] [Module R U']
  [AddCommMonoid V'] [Module R V']
  [AddCommMonoid B''] [Module R B''] [AddCommMonoid U''] [Module R U'']
  [AddCommMonoid V''] [Module R V'']
  {𝒰 : ι → Submodule R U} {𝒱 : κ → Submodule R V} {I : Set ι} {J : Set κ}
  {𝒰' : ι' → Submodule R U'} {𝒱' : κ' → Submodule R V'} {I' : Set ι'} {J' : Set κ'}
  {𝒰'' : ι'' → Submodule R U''} {𝒱'' : κ'' → Submodule R V''}
  {I'' : Set ι''} {J'' : Set κ''}

/-- A morphism of correspondences over two degree maps. It preserves both legs,
homogeneous pieces, admissible degrees and their chosen lifts. -/
@[ext]
structure Hom (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (D : GradedCorrespondence (B := B') 𝒰' 𝒱' I' J') (σ : ι → ι') (τ : κ → κ') where
  /-- The map between the middle modules of the spans. -/
  middle : B →ₗ[R] B'
  /-- The map between the left modules. -/
  left : U →ₗ[R] U'
  /-- The map between the right modules. -/
  right : V →ₗ[R] V'
  /-- The left square commutes. -/
  left_comm : left.comp C.left = D.left.comp middle
  /-- The right square commutes. -/
  right_comm : right.comp C.right = D.right.comp middle
  /-- The left map preserves homogeneous pieces along `σ`. -/
  left_mem : ∀ i x, x ∈ 𝒰 i → left x ∈ 𝒰' (σ i)
  /-- The right map preserves homogeneous pieces along `τ`. -/
  right_mem : ∀ j x, x ∈ 𝒱 j → right x ∈ 𝒱' (τ j)
  /-- Left admissible degrees remain admissible. -/
  admissible_left : Set.MapsTo σ I I'
  /-- Right admissible degrees remain admissible. -/
  admissible_right : Set.MapsTo τ J J'
  /-- The middle map preserves each admissible left lift. -/
  middle_liftLeft : ∀ (i : I) (a : 𝒰 i), middle (C.liftLeft i a) =
    D.liftLeft ⟨σ i, admissible_left i.property⟩ ⟨left a, left_mem i a a.property⟩
  /-- The middle map preserves each admissible right lift. -/
  middle_liftRight : ∀ (j : J) (a : 𝒱 j), middle (C.liftRight j a) =
    D.liftRight ⟨τ j, admissible_right j.property⟩ ⟨right a, right_mem j a a.property⟩

namespace Hom

variable {C : GradedCorrespondence (B := B) 𝒰 𝒱 I J}
  {D : GradedCorrespondence (B := B') 𝒰' 𝒱' I' J'}
  {E : GradedCorrespondence (B := B'') 𝒰'' 𝒱'' I'' J''}
  {σ : ι → ι'} {τ : κ → κ'} {σ' : ι' → ι''} {τ' : κ' → κ''}

attribute [simp] middle_liftLeft middle_liftRight

@[simp] theorem left_comm_apply (f : Hom C D σ τ) (b : B) :
    f.left (C.left b) = D.left (f.middle b) := DFunLike.congr_fun f.left_comm b

@[simp] theorem right_comm_apply (f : Hom C D σ τ) (b : B) :
    f.right (C.right b) = D.right (f.middle b) := DFunLike.congr_fun f.right_comm b

/-- The identity morphism preserves degrees and every chosen lift. -/
def id (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) : Hom C C _root_.id _root_.id where
  middle := LinearMap.id
  left := LinearMap.id
  right := LinearMap.id
  left_comm := by simp
  right_comm := by simp
  left_mem _ _ h := h
  right_mem _ _ h := h
  admissible_left _ h := h
  admissible_right _ h := h
  middle_liftLeft _ _ := rfl
  middle_liftRight _ _ := rfl

@[simp] theorem id_middle : (id C).middle = LinearMap.id := (rfl)
@[simp] theorem id_left : (id C).left = LinearMap.id := (rfl)
@[simp] theorem id_right : (id C).right = LinearMap.id := (rfl)

/-- Compose correspondence morphisms and their degree maps. -/
def comp (g : Hom D E σ' τ') (f : Hom C D σ τ) :
    Hom C E (σ' ∘ σ) (τ' ∘ τ) where
  middle := g.middle.comp f.middle
  left := g.left.comp f.left
  right := g.right.comp f.right
  left_comm := by ext b; simp
  right_comm := by ext b; simp
  left_mem i x hx := g.left_mem _ _ (f.left_mem i x hx)
  right_mem j x hx := g.right_mem _ _ (f.right_mem j x hx)
  admissible_left := g.admissible_left.comp f.admissible_left
  admissible_right := g.admissible_right.comp f.admissible_right
  middle_liftLeft _ _ := by simp
  middle_liftRight _ _ := by simp

@[simp] theorem comp_middle (g : Hom D E σ' τ') (f : Hom C D σ τ) :
    (g.comp f).middle = g.middle.comp f.middle := (rfl)

@[simp] theorem comp_left (g : Hom D E σ' τ') (f : Hom C D σ τ) :
    (g.comp f).left = g.left.comp f.left := (rfl)

@[simp] theorem comp_right (g : Hom D E σ' τ') (f : Hom C D σ τ) :
    (g.comp f).right = g.right.comp f.right := (rfl)

@[simp] theorem id_comp (f : Hom C D σ τ) : (id D).comp f = f := by ext <;> rfl
@[simp] theorem comp_id (f : Hom C D σ τ) : f.comp (id C) = f := by ext <;> rfl

/-- Composition of correspondence morphisms is associative. -/
theorem comp_assoc
    {B''' U''' V''' ι''' κ''' : Type*}
    [AddCommMonoid B'''] [Module R B'''] [AddCommMonoid U'''] [Module R U''']
    [AddCommMonoid V'''] [Module R V''']
    {𝒰''' : ι''' → Submodule R U'''} {𝒱''' : κ''' → Submodule R V'''}
    {I''' : Set ι'''} {J''' : Set κ'''}
    {F : GradedCorrespondence (B := B''') 𝒰''' 𝒱''' I''' J'''}
    {σ'' : ι'' → ι'''} {τ'' : κ'' → κ'''}
    (h : Hom E F σ'' τ'') (g : Hom D E σ' τ') (f : Hom C D σ τ) :
    (h.comp g).comp f = h.comp (g.comp f) := by ext <;> rfl

/-- Reverse the source and target correspondences and exchange the chamber maps. -/
def symm (f : Hom C D σ τ) : Hom C.symm D.symm τ σ where
  middle := f.middle
  left := f.right
  right := f.left
  left_comm := by simpa only [GradedCorrespondence.symm_left] using f.right_comm
  right_comm := by simpa only [GradedCorrespondence.symm_right] using f.left_comm
  left_mem := f.right_mem
  right_mem := f.left_mem
  admissible_left := f.admissible_right
  admissible_right := f.admissible_left
  middle_liftLeft j a := by simpa only [symm_liftLeft] using f.middle_liftRight j a
  middle_liftRight i a := by simpa only [symm_liftRight] using f.middle_liftLeft i a

@[simp] theorem symm_middle (f : Hom C D σ τ) : f.symm.middle = f.middle := (rfl)
@[simp] theorem symm_left (f : Hom C D σ τ) : f.symm.left = f.right := (rfl)
@[simp] theorem symm_right (f : Hom C D σ τ) : f.symm.right = f.left := (rfl)

/-- Reversing a correspondence morphism twice recovers the original morphism after
transporting along the double-reversal equalities for its source and target. -/
@[simp] theorem symm_symm (f : Hom C D σ τ) :
    (cast (by rw [GradedCorrespondence.symm_symm, GradedCorrespondence.symm_symm])
      f.symm.symm : Hom C D σ τ) = f := by
  have aux {C' : GradedCorrespondence (B := B) 𝒰 𝒱 I J}
      {D' : GradedCorrespondence (B := B') 𝒰' 𝒱' I' J'}
      (hC : C' = C) (hD : D' = D) (g : Hom C' D' σ τ)
      (hm : g.middle = f.middle) (hl : g.left = f.left) (hr : g.right = f.right) :
      cast (by rw [hC, hD]) g = f := by
    subst C' D'
    exact Hom.ext hm hl hr
  exact aux (GradedCorrespondence.symm_symm C) (GradedCorrespondence.symm_symm D)
    f.symm.symm rfl rfl rfl

@[simp] theorem symm_id : (id C).symm = id C.symm := by ext <;> rfl

@[simp] theorem symm_comp (g : Hom D E σ' τ') (f : Hom C D σ τ) :
    (g.comp f).symm = g.symm.comp f.symm := by ext <;> rfl

section Transfer

variable [DecidableEq κ] [DecidableEq κ']
  [DirectSum.Decomposition 𝒱] [DirectSum.Decomposition 𝒱']

open Classical in
/-- Transfer naturality under regrading. Every source output degree mapping to `j'`
contributes, including when several degrees merge. Only the input's finite output
support is summed; no finiteness of a degree fiber is required. -/
theorem transfer_map_eq_sum (f : Hom C D σ τ) (i : I) (a : 𝒰 i) (j' : κ') :
    (D.transfer ⟨σ i, f.admissible_left i.property⟩ j'
      ⟨f.left a, f.left_mem i a a.property⟩ : V') =
      ∑ j ∈ (DirectSum.decompose 𝒱 (C.right (C.liftLeft i a))).support with τ j = j',
        f.right (C.transfer i j a : V) := by
  rw [transfer_apply, ← f.middle_liftLeft, ← f.right_comm_apply]
  simpa only [transfer_apply, LinearMap.toAddMonoidHom_coe] using
    DirectSum.decompose_map_eq_sum 𝒱 𝒱' f.right.toAddMonoidHom τ f.right_mem
      (C.right (C.liftLeft i a)) j'

/-- An injective output regrading gives componentwise transfer naturality.
Taking both degree maps to be the identity gives compatibility with truncation. -/
theorem transfer_map_of_injective (f : Hom C D σ τ) (hτ : Function.Injective τ)
    (i : I) (a : 𝒰 i) (j : κ) :
    (D.transfer ⟨σ i, f.admissible_left i.property⟩ (τ j)
      ⟨f.left a, f.left_mem i a a.property⟩ : V') =
        f.right (C.transfer i j a : V) := by
  rw [transfer_apply, ← f.middle_liftLeft, ← f.right_comm_apply, transfer_apply]
  exact (DirectSum.map_decompose_shift 𝒱 𝒱' f.right.toAddMonoidHom τ hτ
    f.right_mem j (C.right (C.liftLeft i a))).symm

end Transfer

section TotalLift

variable [DecidableEq ι] [DecidableEq ι']
  [DirectSum.Decomposition 𝒰] [DirectSum.Decomposition 𝒰']

/-- The middle map sends the zero-extended lift of an admissible homogeneous
input to the zero-extended lift of its image. -/
theorem middle_liftLeftTotal (f : Hom C D σ τ) (i : I) (a : 𝒰 i) :
    f.middle (C.liftLeftTotal a) = D.liftLeftTotal (f.left a) := by
  rw [C.liftLeftTotal_coe, f.middle_liftLeft]
  exact (D.liftLeftTotal_coe ⟨σ i, f.admissible_left i.property⟩
    ⟨f.left a, f.left_mem i a a.property⟩).symm

/-- A morphism intertwines the zero-extended lifts on every input whose
homogeneous support is admissible. The degree map need not be injective;
only the input's finite homogeneous support is summed. -/
theorem middle_liftLeftTotal_of_support (f : Hom C D σ τ)
    (a : U) (ha : ∀ i, DirectSum.decompose 𝒰 a i ≠ 0 → i ∈ I) :
    f.middle (C.liftLeftTotal a) = D.liftLeftTotal (f.left a) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒰 a]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒰 a]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain hiI : i ∈ I := ha i (DFinsupp.mem_support_iff.mp hi)
  exact f.middle_liftLeftTotal ⟨i, hiI⟩ (DirectSum.decompose 𝒰 a i)

/-- A morphism that also maps inadmissible degrees to inadmissible degrees
intertwines the zero-extended lifts on the whole module. Without that extra
hypothesis an inadmissible degree may land on an admissible one, where the
right-hand extension retains a nonzero lift while the left-hand side vanishes. -/
theorem liftLeftTotal_comp_of_mapsTo_compl (f : Hom C D σ τ)
    (hI : Set.MapsTo σ Iᶜ I'ᶜ) :
    D.liftLeftTotal.comp f.left = f.middle.comp C.liftLeftTotal := by
  classical
  ext a
  simp only [LinearMap.comp_apply]
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒰 a]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒰 a]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hiI : i ∈ I
  · exact (f.middle_liftLeftTotal ⟨i, hiI⟩ (DirectSum.decompose 𝒰 a i)).symm
  · have hσ : σ i ∉ I' := hI hiI
    rw [C.liftLeftTotal_of_not_mem hiI (DirectSum.decompose 𝒰 a i).property,
      map_zero,
      D.liftLeftTotal_of_not_mem hσ
        (f.left_mem i (DirectSum.decompose 𝒰 a i) (DirectSum.decompose 𝒰 a i).property)]

/-- Under inadmissibility preservation the whole zero-extended transfer also
intertwines: extending an admissible input, crossing the span and then mapping
commutes with the morphism. -/
theorem right_comp_liftLeftTotal_comp_of_mapsTo_compl (f : Hom C D σ τ)
    (hI : Set.MapsTo σ Iᶜ I'ᶜ) :
    f.right.comp (C.right.comp C.liftLeftTotal) =
      D.right.comp (D.liftLeftTotal.comp f.left) := by
  calc f.right.comp (C.right.comp C.liftLeftTotal)
      = (D.right.comp f.middle).comp C.liftLeftTotal := by
        rw [← LinearMap.comp_assoc, f.right_comm]
    _ = D.right.comp (f.middle.comp C.liftLeftTotal) := LinearMap.comp_assoc _ _ _
    _ = D.right.comp (D.liftLeftTotal.comp f.left) := by
        rw [f.liftLeftTotal_comp_of_mapsTo_compl hI]

end TotalLift

end Hom
end Mei.GradedCorrespondence
