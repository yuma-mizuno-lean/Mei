/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Pentagon
public import Mei.Geometry.ScatteringDiagram.Skew.RankTwo.Assembly

/-!
# The ordered factorization of `Ψ[e₁ + e₂] Ψ[e₁]` to all orders

Take the unimodular plane `ℤ²` with `{e₁, e₂} = 1` and `N° = ℤ²`, with the first quadrant as
allowed monoid and the total degree (`Mei.SkewLatticeDatum.Examples.unitPlane`). The degrees
`x = e₁` and `y = e₁ + e₂` satisfy `{x, y} = 1`, and the additive monoid they generate is the
proper submonoid `{(a + b, b) : a, b ∈ ℕ}` of the quadrant. All ray indices are one on
primitive vectors, so the normalized positive factors are the powers of the dilogarithm
elements `Ψ[m]`.

The product `Ψ[y] Ψ[x]` is antiordered, `{y, x} = -1`. By the pentagon identity
`Ψ[y] Ψ[x] = Ψ[x] Ψ[x + y] Ψ[y]`, and by the uniqueness of
`Mei.SkewLatticeDatum.existsUnique_orderedNormalizedProd_planeDegree_eq`, a family `s` of
natural numbers on the plane degrees `(a, b)` of `x, y` gives the ordered factorization
`∏_{(a, b)} Ψ[a x + b y]^{s(a, b)} = Ψ[y] Ψ[x]` in the angular order exactly when `s` is one at
`(1, 0)`, `(1, 1)`, `(0, 1)` and zero elsewhere
(`Mei.SkewLatticeDatum.Examples.orderedNormalizedProd_planeDegree_eq_iff`).

This is the rank-two Check of the ordinary binomial positivity of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), read as an ordered
factorization to all orders on the monoid of `x` and `y`; compare Nakanishi, *Cluster algebras and
scattering diagrams, Part III*, §5 (arXiv:2111.00800v6).
-/

public section

open TauCeti (PositiveDegrees)

noncomputable section

namespace Mei.SkewLatticeDatum.Examples

open StandardPlane

/-- The weights `(1, 1)` of the total degree. -/
def unitWeight : Weight := ⟨1, 1, one_pos, one_pos⟩

/-- The first quadrant of `ℤ²` with the total degree `a + b`. -/
abbrev unitPlane : PositiveDegrees E.unfrozen := plane unitWeight

/-- The degree `x = e₁`. -/
def pentagonFst : E.NonzeroDegree unitPlane :=
  ⟨⟨(1, 0), mem_unfrozen _⟩, mem_plane_monoid.mpr ⟨zero_le_one, le_rfl⟩,
    fun h => one_ne_zero (congrArg (fun v : Γ => v.1.1) h)⟩

/-- The degree `y = e₁ + e₂`. -/
def pentagonSnd : E.NonzeroDegree unitPlane :=
  ⟨⟨(1, 1), mem_unfrozen _⟩, mem_plane_monoid.mpr ⟨zero_le_one, zero_le_one⟩,
    fun h => one_ne_zero (congrArg (fun v : Γ => v.1.1) h)⟩

/-- The degree `x + y = 2 e₁ + e₂`. -/
def pentagonSum : E.NonzeroDegree unitPlane :=
  ⟨pentagonFst.1 + pentagonSnd.1, add_mem pentagonFst.2.1 pentagonSnd.2.1,
    unitPlane.add_ne_zero pentagonFst.2.1 pentagonSnd.2.1 pentagonFst.2.2⟩

/-- The vector of `x` is `(1, 0)`. -/
@[simp]
theorem coe_pentagonFst : ((pentagonFst : E.unfrozen) : ℤ × ℤ) = (1, 0) := (rfl)

/-- The vector of `y` is `(1, 1)`. -/
@[simp]
theorem coe_pentagonSnd : ((pentagonSnd : E.unfrozen) : ℤ × ℤ) = (1, 1) := (rfl)

/-- The vector of `x + y` is `(2, 1)`. -/
@[simp]
theorem coe_pentagonSum : ((pentagonSum : E.unfrozen) : ℤ × ℤ) = (2, 1) := by
  simp [pentagonSum]

local notation "βℚ" => E.coefficientForm ℚ
local notation "κ" => E.sublattice.toAddSubgroup.rayIndex
local notation "w₀" => E.planeWeight unitPlane pentagonFst pentagonSnd

/-- The pairing `{x, y}` is one. -/
theorem coefficientForm_pentagonFst_pentagonSnd :
    βℚ pentagonFst.1 pentagonSnd.1 = 1 := by
  rw [StandardPlane.coefficientForm_apply]
  simp

/-- The plane degrees `(a, b)` give distinct degrees `a x + b y`. -/
theorem planeDegree_pentagon_injective :
    Function.Injective (E.planeDegree unitPlane pentagonFst pentagonSnd) :=
  E.planeDegree_injective unitPlane pentagonFst pentagonSnd
    (by rw [coefficientForm_pentagonFst_pentagonSnd]; exact one_ne_zero)

/-- The ray index of `x` is one. -/
theorem rayIndex_pentagonFst : κ (pentagonFst.1 : ℤ × ℤ) = 1 :=
  StandardPlane.rayIndex_eq_one_of_form_eq_one ⟨(0, -1), mem_unfrozen _⟩ (by
    rw [form_apply, coe_pentagonFst]
    simp)

/-- The ray index of `y` is one. -/
theorem rayIndex_pentagonSnd : κ (pentagonSnd.1 : ℤ × ℤ) = 1 :=
  StandardPlane.rayIndex_eq_one_of_form_eq_one ⟨(0, -1), mem_unfrozen _⟩ (by
    rw [form_apply, coe_pentagonSnd]
    simp)

/-- The ray index of `x + y` is one. -/
theorem rayIndex_pentagonSum : κ (pentagonSum.1 : ℤ × ℤ) = 1 :=
  StandardPlane.rayIndex_eq_one_of_form_eq_one ⟨(1, 0), mem_unfrozen _⟩ (by
    rw [form_apply, coe_pentagonSum]
    simp)

/-- The plane degree `(1, 0)` of `x, y` is `x`. -/
@[simp]
theorem planeDegree_e₁ :
    E.planeDegree unitPlane pentagonFst pentagonSnd (PlaneDegree.e₁ w₀) = pentagonFst :=
  Subtype.ext (Subtype.ext (by simp))

/-- The plane degree `(0, 1)` of `x, y` is `y`. -/
@[simp]
theorem planeDegree_e₂ :
    E.planeDegree unitPlane pentagonFst pentagonSnd (PlaneDegree.e₂ w₀) = pentagonSnd :=
  Subtype.ext (Subtype.ext (by simp))

/-- The plane degree `(1, 1)` of `x, y` is `x + y`. -/
@[simp]
theorem planeDegree_e₁_add_e₂ :
    E.planeDegree unitPlane pentagonFst pentagonSnd (PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀) =
      pentagonSum :=
  Subtype.ext (Subtype.ext (by simp))

/-- The plane degrees `(1, 0)`, `(1, 1)`, `(0, 1)` of the pentagon identity. -/
def pentagonSupport : Finset (PlaneDegree w₀) :=
  {PlaneDegree.e₁ w₀, PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀, PlaneDegree.e₂ w₀}

/-- The exponents of the ordered factorization of `Ψ[y] Ψ[x]`: one on `pentagonSupport` and zero
elsewhere. -/
def pentagonExponent (q : PlaneDegree w₀) : ℕ := if q ∈ pentagonSupport then 1 else 0

/-- The exponent at a degree of `pentagonSupport` is one. -/
theorem pentagonExponent_of_mem {q : PlaneDegree w₀} (hq : q ∈ pentagonSupport) :
    pentagonExponent q = 1 :=
  ite_eq_left_iff.mpr fun h => absurd hq h

/-- The exponent at `(1, 0)` is one. -/
@[simp]
theorem pentagonExponent_e₁ : pentagonExponent (PlaneDegree.e₁ w₀) = 1 :=
  pentagonExponent_of_mem (by simp [pentagonSupport])

/-- The exponent at `(1, 1)` is one. -/
@[simp]
theorem pentagonExponent_e₁_add_e₂ :
    pentagonExponent (PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀) = 1 :=
  pentagonExponent_of_mem (by simp [pentagonSupport])

/-- The exponent at `(0, 1)` is one. -/
@[simp]
theorem pentagonExponent_e₂ : pentagonExponent (PlaneDegree.e₂ w₀) = 1 :=
  pentagonExponent_of_mem (by simp [pentagonSupport])

/-- The exponent at a degree outside `pentagonSupport` is zero. -/
theorem pentagonExponent_of_notMem {q : PlaneDegree w₀} (hq : q ∉ pentagonSupport) :
    pentagonExponent q = 0 :=
  ite_eq_right_iff.mpr fun h => absurd h hq

/-- The pentagon degrees in the angular order are `(1, 0)`, `(1, 1)`, `(0, 1)`. -/
theorem sort_pentagonSupport :
    pentagonSupport.sort =
      [PlaneDegree.e₁ w₀, PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀, PlaneDegree.e₂ w₀] := by
  have h₁ : PlaneDegree.e₁ w₀ < PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀ :=
    PlaneDegree.lt_of_det_pos (by simp [PlaneDegree.det_eq])
  have h₂ : PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀ < PlaneDegree.e₂ w₀ :=
    PlaneDegree.lt_of_det_pos (by simp [PlaneDegree.det_eq])
  have hsorted : [PlaneDegree.e₁ w₀, PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀,
      PlaneDegree.e₂ w₀].Pairwise (· < ·) := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    exact ⟨⟨h₁, h₁.trans h₂⟩, h₂⟩
  have hfin : pentagonSupport = [PlaneDegree.e₁ w₀, PlaneDegree.e₁ w₀ + PlaneDegree.e₂ w₀,
      PlaneDegree.e₂ w₀].toFinset := by
    simp [pentagonSupport]
  rw [hfin]
  exact (List.toFinset_sort (· ≤ ·) (hsorted.imp ne_of_lt).nodup).mpr (hsorted.imp le_of_lt)

/-- **The ordered factorization of `Ψ[y] Ψ[x]`.** For `x = e₁` and `y = e₁ + e₂` in the
unimodular plane, a family `s` of natural numbers on the plane degrees `(a, b)` satisfies
`∏_{(a, b)} Ψ[a x + b y]^{s(a, b)} = Ψ[y] Ψ[x]`, the product in the angular order, exactly when
`s` is one at `(1, 0)`, `(1, 1)`, `(0, 1)` and zero elsewhere. -/
theorem orderedNormalizedProd_planeDegree_eq_iff (s : PlaneDegree w₀ → ℕ) :
    orderedNormalizedProd planeDegree_pentagon_injective s =
        E.dilogPow unitPlane pentagonSnd 1 * E.dilogPow unitPlane pentagonFst 1 ↔
      s = pentagonExponent := by
  -- Proof plan: the exponents `pentagonExponent` give `Ψ[x] Ψ[x + y] Ψ[y]`, which is `Ψ[y] Ψ[x]`
  -- by the pentagon identity; uniqueness of the ordered factorization gives the converse.
  have hpent : E.dilogPow unitPlane pentagonSnd 1 * E.dilogPow unitPlane pentagonFst 1 =
      E.dilogPow unitPlane pentagonFst 1 * E.dilogPow unitPlane pentagonSum 1 *
        E.dilogPow unitPlane pentagonSnd 1 := by
    simpa only [dilogPow_def, pentagonSum] using SkewLieAlgebra.rayExp_smul_negDilogNeg_pentagon
      βℚ (E.isAlt_coefficientForm ℚ) unitPlane pentagonFst.2.1 pentagonSnd.2.1 pentagonFst.2.2
      pentagonSnd.2.2 (c := 1) (by rw [one_mul, coefficientForm_pentagonFst_pentagonSnd])
  have hexp : orderedNormalizedProd planeDegree_pentagon_injective pentagonExponent =
      E.dilogPow unitPlane pentagonSnd 1 * E.dilogPow unitPlane pentagonFst 1 := by
    rw [hpent, orderedNormalizedProd_def,
      CompletedGroup.orderedProd_eq_list_prod _ _ pentagonSupport fun q hq => ?_,
      sort_pentagonSupport]
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        planeDegree_e₁, planeDegree_e₂, planeDegree_e₁_add_e₂, rayIndex_pentagonFst,
        rayIndex_pentagonSnd, rayIndex_pentagonSum, pentagonExponent_e₁, pentagonExponent_e₂,
        pentagonExponent_e₁_add_e₂, Nat.cast_one, mul_assoc]
    · by_contra hqS
      rw [pentagonExponent_of_notMem hqS, Nat.cast_zero, zero_mul, dilogPow_zero] at hq
      exact hq rfl
  have huniq := E.existsUnique_orderedNormalizedProd_planeDegree_eq unitPlane pentagonFst
    pentagonSnd (by rw [coefficientForm_pentagonFst_pentagonSnd]; exact one_pos)
    [(pentagonSnd, 1), (pentagonFst, 1)] fun p hp => by
      rcases List.mem_pair.mp hp with rfl | rfl
      · exact AddSubmonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact AddSubmonoid.subset_closure (Set.mem_insert _ _)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Nat.cast_one,
    rayIndex_pentagonFst, rayIndex_pentagonSnd] at huniq
  exact ⟨fun h => huniq.unique h hexp, fun h => h ▸ hexp⟩

end Mei.SkewLatticeDatum.Examples
