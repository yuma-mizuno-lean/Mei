/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Hyperplane
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Incoming-chamber rays for the focus-focus slab

A ray ending in its incoming chamber cannot have encountered the slab. We
deduce this from conservation of horizontal velocity and the condition that
bends occur on the slab, without assuming straightness or an encounter bound.
The same argument includes the vertical rays of the invariant monomials.

For a nonzero incoming monomial of nonzero spatial degree, the evaluation fiber
has exactly one decorated ray and its weighted evaluation is that monomial.
Zero coefficients give empty fibers. The zero spatial degree is excluded from
these proper rays: the unit is instead a constant incoming section.

The two incoming Laurent coordinates both use normal exponent `|n|`, whereas
the spatial horizontal exponent is the signed integer `n`. These conventions
agree with `FocusFocus.SlabBrokenLine` in the opposite chamber. We use
`FiniteAffineRay.eq_straight_of_nonneg_hyperplane_time` and
`FiniteAffineRay.eq_straight_of_parallel`. The slab interpretation follows
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties
with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

/-- Local slab-bend conditions force straightness when the endpoint is on the
incoming side. Horizontal exponent zero allows invariant vertical rays. -/
theorem eq_straight_of_incoming_chamber
    (β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)) (n b : ℤ) (Q : ℝ × ℝ)
    (hendpoint : β.endpoint = Q)
    (hincoming : β.incomingDirection = ((n : ℝ), (b : ℝ)))
    (hvertical : ∀ s ∈ β.bends.support, (β.bends s).1 = 0)
    (hslab : ∀ s ∈ β.bends.support, (β s).1 = 0)
    (hoff : Q.1 ≠ 0) (hside : 0 ≤ Q.1 * (n : ℝ)) :
    β = FiniteAffineRay.straight Q ((n : ℝ), (b : ℝ)) := by
  have hd : β.direction.1 = (n : ℝ) := by
    have he := congrArg FiniteAffineRay.incomingDirection
      (β.map_eq_straight (AffineMap.fst : (ℝ × ℝ) →ᵃ[ℝ] ℝ) hvertical)
    simpa only [FiniteAffineRay.incomingDirection_map,
      FiniteAffineRay.incomingDirection_straight, hincoming,
      AffineMap.fst_linear, LinearMap.fst_apply] using he.symm
  have hs : β = FiniteAffineRay.straight β.endpoint β.direction := by
    by_cases hn : (n : ℝ) = 0
    · exact β.eq_straight_of_parallel AffineMap.fst 0 hslab
        (by simpa [hendpoint] using hoff) (by simpa [hd] using hn)
    · apply β.eq_straight_of_nonneg_hyperplane_time AffineMap.fst
        (by simpa [hd] using hn) 0 hslab
      simpa only [AffineMap.coe_fst, AffineMap.fst_linear, LinearMap.fst_apply,
        hendpoint, hd, sub_zero] using (div_nonneg_iff.mpr (mul_nonneg_iff.mp hside))
  have hdirection : β.direction = ((n : ℝ), (b : ℝ)) := by
    have hi : β.incomingDirection = β.direction := by
      simpa only [FiniteAffineRay.incomingDirection_straight] using
        congrArg FiniteAffineRay.incomingDirection hs
    exact hi.symm.trans hincoming
  simpa only [hendpoint, hdirection] using hs

section Rays

variable {R : Type*} [Zero R] (c : R) (n b : ℤ) (Q : ℝ × ℝ)

/-- A nonzero incoming decoration and a ray in its incoming chamber. Only
local bend conditions are imposed; absence of slab encounters is a theorem.
The nonzero spatial degree distinguishes proper rays from constant sections. -/
@[ext]
structure IncomingSlabBrokenLine where
  /-- The geometric realization, with finitely many possible bends. -/
  ray : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)
  /-- Vanishing decorations do not contribute a line. -/
  coefficient_ne_zero : c ≠ 0
  /-- Constant incoming sections are treated separately from proper rays. -/
  exponent_ne_zero : (n, b) ≠ 0
  /-- The endpoint is off the slab. -/
  off_slab : Q.1 ≠ 0
  /-- The endpoint lies on the incoming side, or the direction is vertical. -/
  incoming_side : 0 ≤ Q.1 * (n : ℝ)
  /-- Evaluation at time zero gives the specified endpoint. -/
  endpoint_eq : ray.endpoint = Q
  /-- The incoming spatial direction is prescribed by the monomial. -/
  incomingDirection_eq : ray.incomingDirection = ((n : ℝ), (b : ℝ))
  /-- A slab transfer preserves horizontal velocity. -/
  vertical_bends : ∀ s ∈ ray.bends.support, (ray.bends s).1 = 0
  /-- All actual bends occur on the slab. -/
  slab_bends : ∀ s ∈ ray.bends.support, (ray s).1 = 0

namespace IncomingSlabBrokenLine

variable {c n b Q}

/-- Every incoming-chamber ray is the unique unbent ray of its incoming degree. -/
@[simp]
theorem ray_eq_straight (β : IncomingSlabBrokenLine c n b Q) :
    β.ray = FiniteAffineRay.straight Q ((n : ℝ), (b : ℝ)) :=
  eq_straight_of_incoming_chamber β.ray n b Q β.endpoint_eq β.incomingDirection_eq
    β.vertical_bends β.slab_bends β.off_slab β.incoming_side

instance : Subsingleton (IncomingSlabBrokenLine c n b Q) where
  allEq β γ := IncomingSlabBrokenLine.ext (β.ray_eq_straight.trans γ.ray_eq_straight.symm)

/-- No encounter with the slab occurs, including encounters without a bend. -/
theorem fst_ne_zero (β : IncomingSlabBrokenLine c n b Q) (s : ℝ) (hs : s ≤ 0) :
    (β.ray s).1 ≠ 0 := by
  rw [β.ray_eq_straight, FiniteAffineRay.straight_apply]
  simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  intro he
  rcases mul_nonneg_iff.mp β.incoming_side with h | h
  · have hq : 0 < Q.1 := lt_of_le_of_ne h.1 β.off_slab.symm
    have ht := mul_nonneg (neg_nonneg.mpr hs) h.2
    linarith
  · have hq : Q.1 < 0 := lt_of_le_of_ne h.1 β.off_slab
    have ht := mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hs) h.2
    linarith

/-- The whole ray avoids the affine singularity. -/
theorem avoids_origin (β : IncomingSlabBrokenLine c n b Q) (s : ℝ) (hs : s ≤ 0) :
    β.ray s ≠ 0 := fun he => β.fst_ne_zero s hs (congrArg Prod.fst he)

/-- These rays are proper on every closed incoming half-line, including the
invariant vertical rays with horizontal exponent zero. -/
theorem isProperMap (β : IncomingSlabBrokenLine c n b Q) (a : ℝ) :
    IsProperMap (fun s : Set.Iic a => β.ray s) := by
  apply β.ray.isProperMap_restrict_Iic
  rw [β.incomingDirection_eq]
  intro he
  apply β.exponent_ne_zero
  have hn : (n : ℝ) = 0 := congrArg Prod.fst he
  have hb : (b : ℝ) = 0 := congrArg Prod.snd he
  exact Prod.ext (Int.cast_eq_zero.mp hn) (Int.cast_eq_zero.mp hb)

end IncomingSlabBrokenLine

/-- The incoming monomial has one unbent line when its coefficient and spatial
degree are nonzero and its endpoint is in the incoming chamber. -/
def incomingSlabBrokenLine (hc : c ≠ 0) (hv : (n, b) ≠ 0)
    (hoff : Q.1 ≠ 0) (hside : 0 ≤ Q.1 * (n : ℝ)) : IncomingSlabBrokenLine c n b Q where
  ray := FiniteAffineRay.straight Q ((n : ℝ), (b : ℝ))
  coefficient_ne_zero := hc
  exponent_ne_zero := hv
  off_slab := hoff
  incoming_side := hside
  endpoint_eq := by simp
  incomingDirection_eq := by simp
  vertical_bends := by simp
  slab_bends := by simp

/-- Existence, including zero-coefficient and zero-direction edge cases,
characterizes the complete incoming-chamber evaluation fiber. -/
@[simp]
theorem nonempty_incomingSlabBrokenLine_iff :
    Nonempty (IncomingSlabBrokenLine c n b Q) ↔
      c ≠ 0 ∧ (n, b) ≠ 0 ∧ Q.1 ≠ 0 ∧ 0 ≤ Q.1 * (n : ℝ) :=
  ⟨fun ⟨β⟩ => ⟨β.coefficient_ne_zero, β.exponent_ne_zero, β.off_slab, β.incoming_side⟩,
    fun ⟨hc, hv, hoff, hside⟩ => ⟨incomingSlabBrokenLine c n b Q hc hv hoff hside⟩⟩

/-- The incoming-chamber evaluation fiber is finite for any coefficient type with zero. -/
instance : Fintype (IncomingSlabBrokenLine c n b Q) := Fintype.ofFinite _

end Rays

variable {R : Type*} [Semiring R] (c : R) (n b : ℤ) (Q : ℝ × ℝ)

open AddMonoidAlgebra in
/-- Sum the unchanged entire monomial decoration over the actual incoming fiber. -/
def incomingSlabWeightedEvaluation : R[ℤ × ℤ] :=
  ∑ _β : IncomingSlabBrokenLine c n b Q, single ((n.natAbs : ℤ), b) c

open AddMonoidAlgebra in
/-- Weighted evaluation sums the decorations over the incoming evaluation fiber. -/
theorem incomingSlabWeightedEvaluation_def :
    incomingSlabWeightedEvaluation c n b Q =
      ∑ _β : IncomingSlabBrokenLine c n b Q, single ((n.natAbs : ℤ), b) c := (rfl)

open AddMonoidAlgebra in
/-- In its incoming chamber, weighted evaluation of a nonconstant incoming
monomial is that monomial. At other endpoints, or for zero spatial degree,
the proper-ray fiber is empty. Zero coefficients give zero in every case. -/
@[simp]
theorem incomingSlabWeightedEvaluation_eq :
    incomingSlabWeightedEvaluation c n b Q =
      if (n, b) ≠ 0 ∧ Q.1 ≠ 0 ∧ 0 ≤ Q.1 * (n : ℝ) then
        single ((n.natAbs : ℤ), b) c else 0 := by
  classical
  split_ifs with h
  · obtain ⟨hv, hoff, hside⟩ := h
    by_cases hc : c = 0
    · simp [incomingSlabWeightedEvaluation, hc]
    · let β := incomingSlabBrokenLine c n b Q hc hv hoff hside
      let : Unique (IncomingSlabBrokenLine c n b Q) := ⟨⟨β⟩, fun _ => Subsingleton.elim _ _⟩
      simp [incomingSlabWeightedEvaluation]
  · have : IsEmpty (IncomingSlabBrokenLine c n b Q) :=
      ⟨fun β => h ⟨β.exponent_ne_zero, β.off_slab, β.incoming_side⟩⟩
    simp [incomingSlabWeightedEvaluation]

end Mei.FocusFocus
