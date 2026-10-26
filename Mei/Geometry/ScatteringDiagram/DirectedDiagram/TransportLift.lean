/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Algebra.Lie.BCH.CentralExtension
public import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Lifted transport and central defects of directed diagrams

Let a directed diagram be consistent at order `k`. A `TransportLift` chooses, at
every point off the walls active at order `k + 1`, an element of the order-`(k + 1)`
BCH group projecting to the order-`k` transport from a fixed base point. Such lifts
exist because the truncation maps are surjective, and the order-`(k + 1)` transport
is one when the diagram is consistent at that order.

The *central defect* of an order-`(k + 1)` admissible path `p` from `y` to `z` is
`log (t z⁻¹ * P * t y)`, where `P` is its path product. Lower-order consistency
places it in the central kernel of the truncation map, which is abelian. Defects
add under concatenation, negate under reversal, change by a coboundary when the
lifts change, and around a loop equal the logarithm of the loop product. Hence
consistency at order `k + 1` is equivalent to the defect being a coboundary.
For a segment crossing a single regular wall germ, the defect is computed from the
combined label of that germ: this is the codimension-one central defect
`log (t₊⁻¹ * X * t₋)` of a chamber trivialization.

The algebra is `LieHom.logDefect`, together with the centrality of successive
truncation kernels, `PositiveDegrees.ker_truncationMap_succ_le_center`. These
defects are the order-by-order obstructions of the inductive construction of
consistent completions in Travis Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), proof of Theorem 2.6,
and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
[arXiv:1411.1394v2](https://arxiv.org/abs/1411.1394v2), Appendix C.3.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  (k : ℕ) (hk : D.LevelConsistent k)
  (x₀ : WallComplement (fun j : D.active (k + 1) => (D.wall j).support))

/-- Lifts to order `k + 1` of the order-`k` endpoint transport from the base point
`x₀`, at every point off the walls active at order `k + 1`. -/
@[ext]
structure TransportLift where
  /-- The lift at a point off the walls active at order `k + 1`. -/
  toFun : WallComplement (fun j : D.active (k + 1) => (D.wall j).support) →
    d.truncatedGroup ℒ (k + 1)
  /-- Each lift projects to the lower-order transport from the base point. -/
  truncation_toFun (y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)) :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (toFun y) =
      D.levelTransport k hk
        ((WallComplement.restrictPrefunctor (fun j : D.active (k + 1) => (D.wall j).support)
          (Set.inclusion (D.active_mono (Nat.le_succ k)))).obj x₀)
        ((WallComplement.restrictPrefunctor (fun j : D.active (k + 1) => (D.wall j).support)
          (Set.inclusion (D.active_mono (Nat.le_succ k)))).obj y)

namespace TransportLift

variable {D k hk x₀}

instance : CoeFun (D.TransportLift k hk x₀)
    (fun _ => WallComplement (fun j : D.active (k + 1) => (D.wall j).support) →
      d.truncatedGroup ℒ (k + 1)) where
  coe t := t.toFun

/-- A lift projects to the lower-order transport from the base point. -/
@[simp]
theorem truncation_apply (t : D.TransportLift k hk x₀)
    (y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)) :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t y) =
      D.levelTransport k hk
        ((WallComplement.restrictPrefunctor (fun j : D.active (k + 1) => (D.wall j).support)
          (Set.inclusion (D.active_mono (Nat.le_succ k)))).obj x₀)
        ((WallComplement.restrictPrefunctor (fun j : D.active (k + 1) => (D.wall j).support)
          (Set.inclusion (D.active_mono (Nat.le_succ k)))).obj y) :=
  t.truncation_toFun y

variable (D k hk x₀) in
/-- Lower-order transport always lifts, by surjectivity of the truncation map. -/
instance : Nonempty (D.TransportLift k hk x₀) := by
  choose t ht using fun y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support) =>
    LieHom.bchGroupMap_surjective (d.truncationMap_surjective ℒ (Nat.le_succ k))
      (D.levelTransport k hk
        ((WallComplement.restrictPrefunctor (fun j : D.active (k + 1) => (D.wall j).support)
          (Set.inclusion (D.active_mono (Nat.le_succ k)))).obj x₀)
        ((WallComplement.restrictPrefunctor (fun j : D.active (k + 1) => (D.wall j).support)
          (Set.inclusion (D.active_mono (Nat.le_succ k)))).obj y))
  exact ⟨⟨t, ht⟩⟩

variable (hk x₀) in
/-- At a consistent order `k + 1`, its own transport from the base point is a lift. -/
def ofLevelTransport (hk' : D.LevelConsistent (k + 1)) : D.TransportLift k hk x₀ where
  toFun := D.levelTransport (k + 1) hk' x₀
  truncation_toFun := D.truncation_levelTransport (Nat.le_succ k) hk hk' x₀

@[simp]
theorem ofLevelTransport_apply (hk' : D.LevelConsistent (k + 1))
    (y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)) :
    ofLevelTransport hk x₀ hk' y = D.levelTransport (k + 1) hk' x₀ y := (rfl)

variable {y z w : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}

/-- An order-`(k + 1)` path product carries the lift at its source to the lift at its
target after truncation. -/
theorem truncation_levelPathProduct_mul (t : D.TransportLift k hk x₀)
    (p : AdmissiblePLPath y z) :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (D.levelPathProduct (k + 1) p) *
        (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t y) =
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t z) := by
  rw [D.truncation_levelPathProduct (Nat.le_succ k) p, t.truncation_apply, t.truncation_apply,
    ← D.levelTransport_eq_levelPathProduct hk, ← D.levelTransport_comp]

/-- The central defect of an order-`(k + 1)` admissible path: the logarithm of its
path product gauged by the lifts at its endpoints, in the kernel of truncation. -/
def defect (t : D.TransportLift k hk x₀) (p : AdmissiblePLPath y z) :
    (d.truncationMap ℒ (Nat.le_succ k)).ker :=
  (d.truncationMap ℒ (Nat.le_succ k)).logDefect (t y) (t z) (D.levelPathProduct (k + 1) p)
    (t.truncation_levelPathProduct_mul p)

/-- The defect is the logarithm of the gauged path product. -/
@[simp]
theorem coe_defect (t : D.TransportLift k hk x₀) (p : AdmissiblePLPath y z) :
    (t.defect p : d.truncatedLie ℒ (k + 1)) =
      BCHGroup.log ((t z)⁻¹ * D.levelPathProduct (k + 1) p * t y) :=
  LieHom.coe_logDefect _ _ _ _ _

/-- Two paths with the same endpoints have equal defects exactly when they have equal
order-`(k + 1)` path products. -/
theorem defect_eq_defect_iff (t : D.TransportLift k hk x₀) (p q : AdmissiblePLPath y z) :
    t.defect p = t.defect q ↔ D.levelPathProduct (k + 1) p = D.levelPathProduct (k + 1) q := by
  refine ⟨fun he => ?_, fun he => by simp only [defect, he]⟩
  have he' := congrArg Subtype.val he
  rw [coe_defect, coe_defect] at he'
  simpa using BCHGroup.log_injective he'

/-- A defect vanishes exactly when the path product is the quotient of the lifts. -/
@[simp]
theorem defect_eq_zero_iff (t : D.TransportLift k hk x₀) (p : AdmissiblePLPath y z) :
    t.defect p = 0 ↔ D.levelPathProduct (k + 1) p = t z * (t y)⁻¹ :=
  LieHom.logDefect_eq_zero_iff _ _ _ _ _

/-- The constant path has zero defect. -/
@[simp]
theorem defect_nil (t : D.TransportLift k hk x₀) :
    t.defect (Quiver.Path.nil : AdmissiblePLPath y y) = 0 := by
  simp

/-- Defects add under concatenation, the later path on the left. -/
@[simp]
theorem defect_comp (t : D.TransportLift k hk x₀) (p : AdmissiblePLPath y z)
    (q : AdmissiblePLPath z w) :
    t.defect (p.comp q) = t.defect q + t.defect p := by
  have he := (d.truncationMap ℒ (Nat.le_succ k)).logDefect_mul (t y) (t z) (t w)
    (D.levelPathProduct (k + 1) p) (D.levelPathProduct (k + 1) q)
    (t.truncation_levelPathProduct_mul p) (t.truncation_levelPathProduct_mul q)
  apply Subtype.ext
  simpa only [coe_defect, LieSubmodule.coe_add, LieHom.coe_logDefect, levelPathProduct_comp]
    using congrArg Subtype.val he

/-- Reversing a path negates its defect. -/
@[simp]
theorem defect_reverse (t : D.TransportLift k hk x₀) (p : AdmissiblePLPath y z) :
    t.defect p.reverse = -t.defect p := by
  have he := (d.truncationMap ℒ (Nat.le_succ k)).logDefect_inv (t y) (t z)
    (D.levelPathProduct (k + 1) p) (t.truncation_levelPathProduct_mul p)
  apply Subtype.ext
  simpa only [coe_defect, LieSubmodule.coe_neg, LieHom.coe_logDefect, levelPathProduct_reverse]
    using congrArg Subtype.val he

/-- Around a loop the defect is the logarithm of the loop product, independently of
the lifts: the loop product is central. -/
theorem coe_defect_of_loop (t : D.TransportLift k hk x₀) (p : AdmissiblePLPath y y) :
    (t.defect p : d.truncatedLie ℒ (k + 1)) = BCHGroup.log (D.levelPathProduct (k + 1) p) := by
  let f := d.truncationMap ℒ (Nat.le_succ k)
  have hker : D.levelPathProduct (k + 1) p ∈ f.bchGroupMap.ker :=
    MonoidHom.mem_ker.mpr (mul_eq_right.mp (t.truncation_levelPathProduct_mul p))
  have hc := Subgroup.mem_center_iff.mp
    (f.ker_bchGroupMap_le_center (d.ker_truncationMap_succ_le_center ℒ k) hker) (t y)⁻¹
  rw [coe_defect, hc, inv_mul_cancel_right]

/-- Consistency at order `k + 1` is equivalent to endpoint independence of defects. -/
theorem levelConsistent_succ_iff_defect_eq (t : D.TransportLift k hk x₀) :
    D.LevelConsistent (k + 1) ↔
      ∀ ⦃y z : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)⦄
        (p q : AdmissiblePLPath y z), t.defect p = t.defect q := by
  simp only [levelConsistent_def, defect_eq_defect_iff]

/-- Consistency at order `k + 1` is equivalent to vanishing of all loop defects. -/
theorem levelConsistent_succ_iff_defect_loop (t : D.TransportLift k hk x₀) :
    D.LevelConsistent (k + 1) ↔
      ∀ (y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
        (p : AdmissiblePLPath y y), t.defect p = 0 := by
  rw [levelConsistent_iff_loops]
  refine forall₂_congr fun y p => ?_
  rw [← Subtype.val_inj, coe_defect_of_loop, ZeroMemClass.coe_zero]
  exact ⟨fun he => by rw [he, BCHGroup.log_one], fun he => by
    simpa using congrArg BCHGroup.exp he⟩

/-- The order-`(k + 1)` transport has zero defects. -/
@[simp]
theorem defect_ofLevelTransport (hk' : D.LevelConsistent (k + 1)) (p : AdmissiblePLPath y z) :
    (ofLevelTransport hk x₀ hk').defect p = 0 := by
  rw [defect_eq_zero_iff, ofLevelTransport_apply, ofLevelTransport_apply,
    ← D.levelTransport_swap, ← D.levelTransport_comp, D.levelTransport_eq_levelPathProduct hk' p]

/-- The kernel element relating two lifts at a point: the logarithm of `(t y)⁻¹ * t' y`. -/
def gauge (t t' : D.TransportLift k hk x₀)
    (y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)) :
    (d.truncationMap ℒ (Nat.le_succ k)).ker :=
  Multiplicative.toAdd ((d.truncationMap ℒ (Nat.le_succ k)).kernelLogEquiv
    ⟨(t y)⁻¹ * t' y, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, t.truncation_apply, t'.truncation_apply,
        inv_mul_cancel]⟩)

/-- The gauge is the logarithm of the quotient of the lifts. -/
@[simp]
theorem coe_gauge (t t' : D.TransportLift k hk x₀)
    (y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)) :
    (t.gauge t' y : d.truncatedLie ℒ (k + 1)) = BCHGroup.log ((t y)⁻¹ * t' y) :=
  LieHom.coe_kernelLogEquiv _ _

/-- A lift is recovered from another by multiplying with the exponential of the gauge. -/
theorem mul_exp_gauge (t t' : D.TransportLift k hk x₀)
    (y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)) :
    t y * BCHGroup.exp (t.gauge t' y : d.truncatedLie ℒ (k + 1)) = t' y := by
  rw [coe_gauge, BCHGroup.exp_log, mul_inv_cancel_left]

/-- Changing lifts changes defects by the coboundary of the gauge. -/
theorem defect_eq_add_gauge_sub_gauge (t t' : D.TransportLift k hk x₀)
    (p : AdmissiblePLPath y z) :
    t'.defect p = t.defect p + t.gauge t' y - t.gauge t' z := by
  have he := (d.truncationMap ℒ (Nat.le_succ k)).logDefect_change_lifts (t y) (t z)
    (D.levelPathProduct (k + 1) p) (t.truncation_levelPathProduct_mul p)
    (t.gauge t' y) (t.gauge t' z)
  apply Subtype.ext
  have he' := congrArg Subtype.val he
  simp only [LieHom.coe_logDefect, mul_exp_gauge] at he'
  simpa only [coe_defect, LieSubmodule.coe_sub, LieSubmodule.coe_add,
    LieHom.coe_logDefect] using he'

/-- Consistency at order `k + 1` is equivalent to the defect being a coboundary:
lower-order consistency extends exactly when the defect can be gauged away. -/
theorem levelConsistent_succ_iff_exists_coboundary (t : D.TransportLift k hk x₀) :
    D.LevelConsistent (k + 1) ↔
      ∃ c : WallComplement (fun j : D.active (k + 1) => (D.wall j).support) →
          (d.truncationMap ℒ (Nat.le_succ k)).ker,
        ∀ ⦃y z : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)⦄
          (p : AdmissiblePLPath y z), t.defect p = c y - c z := by
  refine ⟨fun hk' => ⟨fun y => -t.gauge (ofLevelTransport hk x₀ hk') y, fun y z p => ?_⟩,
    fun ⟨c, hc⟩ => ?_⟩
  · have he := t.defect_eq_add_gauge_sub_gauge (ofLevelTransport hk x₀ hk') p
    rw [defect_ofLevelTransport, eq_comm, sub_eq_zero] at he
    rw [neg_sub_neg, eq_sub_iff_add_eq, he]
  · exact (t.levelConsistent_succ_iff_defect_loop).mpr fun y p => by rw [hc, sub_self]

/-- Across a single regular wall germ the defect is computed by the combined label:
it is the central defect `log (t₊⁻¹ * X * t₋)` of the oriented crossing. -/
theorem coe_defect_toPath_eq_combinedLabel (t : D.TransportLift k hk x₀) (e : y ⟶ z) (θ : V)
    (hθ : θ ∉ singularSupport (fun j : D.active (k + 1) => (D.wall j).support))
    (s : ℝ) (hcross : ∀ j r, (j, r) ∈ crossings y z ↔ θ ∈ (D.wall j).support ∧ r = s) :
    (t.defect e.toPath : d.truncatedLie ℒ (k + 1)) =
      BCHGroup.log ((t z)⁻¹ * D.combinedLabel (k + 1) θ (z.val - y.val) hθ * t y) := by
  rw [coe_defect, D.levelPathProduct_toPath_eq_combinedLabel (k + 1) e θ hθ s hcross]

end TransportLift

end Mei.DirectedDiagram
