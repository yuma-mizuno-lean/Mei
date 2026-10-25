/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Basic
public import Mei.Algebra.Lie.Free.Grading

/-!
# Vanishing of tangent-degree wall Lie words

A bracketed word of wall elements has a recursively determined integral normal.
If all leaf normals annihilate a subgroup of tangent vectors, so does every
intermediate normal. A word with at least two leaves therefore vanishes when its
total geometric degree belongs to that subgroup. In particular, every such word
of zero geometric direction vanishes.

To apply the result to a real subspace, take its inverse image in the tangent
lattice. Words are Mathlib's `FreeMagma`; their evaluation uses
`Mei.FreeLieAlgebra.word` and Mathlib's `FreeLieAlgebra.lift`, rather than a
second evaluator. Total degrees use `FreeMagma.lift` into the multiplicative
synonym of the degree monoid.
-/

public section

namespace Mei

open Multiplicative

variable {Γ Λ R L S : Type*} [AddCommMonoid Γ]

local notation "deg" => fun (d : S → Γ) (w : FreeMagma S) =>
  toAdd (FreeMagma.lift (ofAdd ∘ d) w)

section Normals

variable [AddCommMonoid Λ]

/-- The integral normal of a homogeneous bracketed wall word. -/
def wallWordNormal (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ) :
    FreeMagma S → (Λ →+ ℤ)
  | .of s => m s
  | .mul u v => wallBracketNormal ρ (deg d u) (deg d v)
      (wallWordNormal ρ d m u) (wallWordNormal ρ d m v)

/-- A leaf retains its prescribed normal. -/
@[simp]
theorem wallWordNormal_of (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ) (s : S) :
    wallWordNormal ρ d m (FreeMagma.of s) = m s := (rfl)

/-- Bracketing words contracts their normals against each other's total degrees. -/
@[simp]
theorem wallWordNormal_mul (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ)
    (u v : FreeMagma S) :
    wallWordNormal ρ d m (u * v) = wallBracketNormal ρ (deg d u) (deg d v)
      (wallWordNormal ρ d m u) (wallWordNormal ρ d m v) := (rfl)

/-- A word normal annihilates every vector annihilated by all leaf normals. -/
theorem wallWordNormal_apply_eq_zero (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ)
    (v : Λ) (hm : ∀ s, m s v = 0) (w : FreeMagma S) :
    wallWordNormal ρ d m w v = 0 := by
  induction w with
  | ih1 s => exact hm s
  | ih2 u v hu hv => simp [hu, hv]

end Normals

namespace DirectedWallSpaces

variable [AddCommGroup Λ] [CommRing R] [LieRing L] [LieAlgebra R L]

variable {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  (d : S → Γ) (m : S → Λ →+ ℤ) (a : S → L)

local notation "eval" => fun w =>
  _root_.FreeLieAlgebra.lift R a (Mei.FreeLieAlgebra.word R w)

/-- Evaluation of a homogeneous wall word belongs to its recursively specified wall space. -/
theorem word_mem_wall (ha : ∀ s, a s ∈ H.wall (d s) (m s)) (w : FreeMagma S) :
    eval w ∈ H.wall (deg d w) (wallWordNormal ρ d m w) := by
  induction w with
  | ih1 s => simpa using ha s
  | ih2 u v hu hv =>
    simpa only [Mei.FreeLieAlgebra.word_mul, LieHom.map_lie, wallWordNormal_mul,
      map_mul, toAdd_mul] using H.bracket_mem hu hv

/-- A wall Lie word with at least two leaves vanishes if its total geometric degree
lies in a subgroup annihilated by every leaf normal. -/
theorem word_eq_zero_of_direction_mem (ha : ∀ s, a s ∈ H.wall (d s) (m s))
    (W : AddSubgroup Λ) (hm : ∀ s v, v ∈ W → m s v = 0)
    (w : FreeMagma S) (hw : 2 ≤ w.length) (hdegree : ρ (deg d w) ∈ W) :
    eval w = 0 := by
  cases w with
  | of s => simp [FreeMagma.length] at hw
  | mul u v =>
    have htotal : ρ (deg d u + deg d v) ∈ W := by
      simpa only [FreeMagma.mul_eq, map_mul, toAdd_mul] using hdegree
    have hu := H.word_mem_wall d m a ha u
    have hv := H.word_mem_wall d m a ha v
    have hnormal (z : FreeMagma S) :
        wallWordNormal ρ d m z (ρ (deg d u + deg d v)) = 0 :=
      wallWordNormal_apply_eq_zero ρ d m _ (fun s => hm s _ htotal) z
    simpa only [FreeMagma.mul_eq, Mei.FreeLieAlgebra.word_mul, LieHom.map_lie] using
      H.lie_eq_zero_of_normal_total_eq_zero hu hv (hnormal u) (hnormal v)

/-- Every wall Lie word with at least two leaves and zero total geometric direction vanishes. -/
theorem word_eq_zero_of_direction_eq_zero (ha : ∀ s, a s ∈ H.wall (d s) (m s))
    (w : FreeMagma S) (hw : 2 ≤ w.length) (hdegree : ρ (deg d w) = 0) :
    eval w = 0 := by
  exact H.word_eq_zero_of_direction_mem d m a ha ⊥
    (fun s v hv => by simpa only [AddSubgroup.mem_bot.mp hv] using (m s).map_zero)
    w hw (by simpa only [AddSubgroup.mem_bot] using hdegree)

end DirectedWallSpaces

end Mei
