/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord

/-!
# Deleting walls from geometric crossing words

An admissible path for a finite polyhedral complex remains admissible after
passing to any complex whose walls are a subset, in particular a subcomplex.
Its ordered crossings are obtained by deleting exactly
the absent walls, with all retained crossing times unchanged. Accordingly its
signed crossing word is the image of the original word under the homomorphism
which kills the deleted generators.

This allows wall labels equal to the identity to be discarded before evaluating
path products. It uses Mathlib's `Prefunctor.mapPath`, `FreeGroup.lift` and list
filtering, together with Mei's geometric characterization of ordered crossings.
All maps retain the original affine chain.
-/

public section

noncomputable section

open Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C D : FinitePolyhedralComplex h}

/-- The free-group homomorphism retaining the walls of `D` and killing all others. -/
def wallDeletion (C D : FinitePolyhedralComplex h) : FreeGroup C.walls →* FreeGroup D.walls :=
  FreeGroup.lift fun P => if hP : P.val ∈ D.walls then FreeGroup.of ⟨P.val, hP⟩ else 1

/-- Deletion on a wall generator is determined by its actual carrier. -/
@[simp]
theorem wallDeletion_of (P : C.walls) :
    C.wallDeletion D (FreeGroup.of P) =
      if hP : P.val ∈ D.walls then FreeGroup.of ⟨P.val, hP⟩ else 1 := by
  simp [wallDeletion]

/-- Deleting no walls is the identity homomorphism. -/
@[simp]
theorem wallDeletion_self (C : FinitePolyhedralComplex h) :
    C.wallDeletion C = MonoidHom.id _ := by
  apply FreeGroup.lift.symm.injective
  funext P
  simp [wallDeletion]

variable (hW : D.walls ⊆ C.walls)

local notation "r" => WallComplement.restrictPrefunctor
  (fun P : C.walls => (Subtype.val P : Set V))
  (fun P : D.walls => (Subtype.mk (Subtype.val P)
    (hW (Subtype.property P)) : C.walls))

variable {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Deleting walls filters the geometric crossing list, without changing times. -/
theorem orderedCrossings_restrict (e : x ⟶ y) :
    D.orderedCrossings ((r).map e) = (C.orderedCrossings e).filterMap
      (fun a => if hP : a.1.val ∈ D.walls then some (⟨a.1.val, hP⟩, a.2) else none) := by
  classical
  let f : C.walls × ℝ → Option (D.walls × ℝ) :=
    fun a => if hP : a.1.val ∈ D.walls then some (⟨a.1.val, hP⟩, a.2) else none
  have hsome (a : C.walls × ℝ) (b : D.walls × ℝ) :
      f a = some b ↔ a.1.val = b.1.val ∧ a.2 = b.2 := by
    rcases b with ⟨⟨Q, hQ⟩, t⟩
    dsimp [f]
    split_ifs with ha
    · simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    · simp only [false_iff, not_and]
      intro hab
      exact (ha (hab ▸ hQ)).elim
  symm
  apply (D.orderedCrossings_eq_iff ((r).map e) _).mpr
  constructor
  · exact (C.pairwise_orderedCrossings e).filterMap f (by
      intro a a' haa b hb b' hb'
      rw [hsome] at hb hb'
      simpa only [← hb.2, ← hb'.2] using haa)
  · intro b
    rcases b with ⟨P, t⟩
    simp only [List.mem_filterMap]
    constructor
    · rintro ⟨a, ha, hf⟩
      obtain ⟨hab, hat⟩ := (hsome a (P, t)).mp hf
      have ha' := (WallComplement.mem_crossings x y a.1 a.2).mp
        ((C.mem_orderedCrossings e a).mp ha)
      rw [WallComplement.mem_crossings]
      simpa only [WallComplement.restrictPrefunctor_obj_val, Function.comp_apply,
        hab, hat] using ha'
    · intro hb
      refine ⟨(⟨P.val, hW P.property⟩, t),
        (C.mem_orderedCrossings e _).mpr ?_, (hsome _ _).mpr ⟨rfl, rfl⟩⟩
      simpa only [WallComplement.mem_crossings, WallComplement.restrictPrefunctor_obj_val,
        Function.comp_apply] using hb

/-- Wall deletion carries the segment word to the word of the same geometric segment
in the smaller wall family, with the restricted normals. -/
@[simp]
theorem segmentCrossingWord_restrict (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) :
    D.segmentCrossingWord
        (fun P => ν ⟨P.val, hW P.property⟩) ((r).map e) =
      C.wallDeletion D (C.segmentCrossingWord ν e) := by
  classical
  let f : C.walls × ℝ → Option (D.walls × ℝ) :=
    fun a => if hP : a.1.val ∈ D.walls then some (⟨a.1.val, hP⟩, a.2) else none
  have hl (l : List (C.walls × ℝ)) :
      ((l.filterMap f).map fun a => D.crossingLetter
        (fun P => ν ⟨P.val, hW P.property⟩) ((r).obj x) ((r).obj y) a.1).prod =
      C.wallDeletion D ((l.map fun a => C.crossingLetter ν x y a.1).prod) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      by_cases ha : a.1.val ∈ D.walls
      · have he : (⟨a.1.val, hW ha⟩ : C.walls) = a.1 := Subtype.ext rfl
        have hf : f a = some (⟨a.1.val, ha⟩, a.2) := by simp only [f, dite_eq_left ha]
        rw [List.filterMap_cons_some hf]
        simp only [List.map_cons, List.prod_cons, map_mul, ih]
        congr 1
        simp only [D.crossingLetter_def, C.crossingLetter_def,
          WallComplement.restrictPrefunctor_obj_val, he]
        split_ifs <;> simp only [map_inv, wallDeletion_of, dite_eq_left ha]
      · have hf : f a = none := by simp only [f, dite_eq_right ha]
        rw [List.filterMap_cons_none hf]
        rw [List.map_cons, List.prod_cons, map_mul]
        have hz : C.wallDeletion D (C.crossingLetter ν x y a.1) = 1 := by
          simp only [C.crossingLetter_def]
          split_ifs <;> simp [ha]
        rw [hz, one_mul]
        exact ih
  simpa only [D.segmentCrossingWord_def, C.segmentCrossingWord_def,
    orderedCrossings_restrict hW e, ← List.filterMap_reverse] using
      hl (C.orderedCrossings e).reverse

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C D : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Forgetting walls in an admissible polygonal path kills precisely their free-group
generators in its crossing word. -/
@[simp]
theorem crossingWord_restrict (p : AdmissiblePLPath x y) (hW : D.walls ⊆ C.walls)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    ((WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
      (fun P : D.walls => (⟨P.val, hW P.property⟩ : C.walls))).mapPath p).crossingWord
        (fun P => ν ⟨P.val, hW P.property⟩) =
      C.wallDeletion D (p.crossingWord ν) := by
  induction p with
  | nil => simp only [Prefunctor.mapPath_nil, crossingWord_nil (C := D),
      crossingWord_nil (C := C), map_one]
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, crossingWord_cons (C := D),
      crossingWord_cons (C := C), map_mul, ih,
      Mei.FinitePolyhedralComplex.segmentCrossingWord_restrict hW ν e]

end Quiver.Path
