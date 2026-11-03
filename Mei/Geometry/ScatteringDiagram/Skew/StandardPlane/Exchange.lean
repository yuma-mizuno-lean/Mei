/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Integral
public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Rebase
public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Shape
public import Mei.Geometry.ScatteringDiagram.Skew.Pentagon
public import Mei.Algebra.Lie.BCH.Ordering

/-!
# Exchange of antiordered unit factors in the standard plane

If plane degrees `x, y` form an inversion, `{x, y} < 0`, the unit factors satisfy
`Ψ[x] Ψ[y] = Ψ[y] M Ψ[x]` at every finite order, where `M` is a product of unit factors of
plane degrees in the open quadrant that have larger weighted degree than `x` and `y`
(`exists_exchange`). This is the exchange needed to order products of dilogarithm labels.

Write `D = {y, x}`. For `D = 1` it is the pentagon identity. For `D ≥ 2` rescale the plane
along `x, y` (`Mei.StandardPlane.rebaseMap`): then `Ψ[x]^{κ(x)}` and `Ψ[y]^{κ(y)}` are the
powers `Ψ[e₂]^A` and `Ψ[e₁]^B` of the rescaled plane, with `A = κ(x) D` and `B = κ(y) D` positive
integers. The ordering algorithm in the rescaled plane
(`PositiveDegrees.exists_isChain_projection_prod_eq_of_exchange`), whose own exchanges lie in a
plane of strictly larger weights and are available by induction, turns `Ψ[e₂]^A Ψ[e₁]^B` into
`Ψ[e₁]^B I Ψ[e₂]^A` for an ordered list `I` in the open quadrant. Carrying this back,
`Ψ[x] Ψ[y] = Ψ[y] M' Ψ[x]` with `M'` a product of the labels `Ψ[T i]^{κ(i) / D}`, `i ∈ I`,
and these regroup into unit factors by the integrality of the exponents
(`exists_units_prod_eq_of_isChain`).

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2, the ordering
  algorithm for rank two products of dilogarithm elements, its reduction to the pentagon
  identity after rescaling the form, and the integrality of the exponents of its output
  (arXiv:2111.00800v6).
* Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3, for
  the positivity of the ordered factorization (arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples PowerSeries

local notation "β" => E.coefficientForm ℚ
local notation "hβ" => E.isAlt_coefficientForm ℚ

variable {w : Weight}

/-- The sum `x + y` of two plane degrees. -/
private def PlaneDegree.add (x y : PlaneDegree w) : PlaneDegree w where
  vec := x.vec + y.vec
  mem := add_mem x.mem y.mem
  ne_zero h := by
    have h1 : x.fst + y.fst = 0 := congrArg (fun v : Γ => v.1.1) h
    have h2 : x.snd + y.snd = 0 := congrArg (fun v : Γ => v.1.2) h
    have := y.fst_nonneg
    have := x.fst_nonneg
    have := y.snd_nonneg
    have := x.snd_nonneg
    rcases y.fst_ne_zero_or with h | h <;> omega

-- The sum has vector `x.vec + y.vec` by construction and the coordinates of a sum in `ℤ × ℤ` are
-- the sums of the coordinates, so the next three lemmas hold by unfolding `PlaneDegree.add`.
@[simp]
private theorem PlaneDegree.add_fst (x y : PlaneDegree w) :
    (PlaneDegree.add x y).fst = x.fst + y.fst := (rfl)
@[simp]
private theorem PlaneDegree.add_snd (x y : PlaneDegree w) :
    (PlaneDegree.add x y).snd = x.snd + y.snd := (rfl)

private theorem PlaneDegree.deg_add (x y : PlaneDegree w) :
    (PlaneDegree.add x y).deg = x.deg + y.deg := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [PlaneDegree.deg_eq, PlaneDegree.deg_eq, PlaneDegree.deg_eq, PlaneDegree.add_fst,
    PlaneDegree.add_snd]
  ring

@[simp]
private theorem PlaneDegree.add_vec (x y : PlaneDegree w) :
    (PlaneDegree.add x y).vec = x.vec + y.vec := (rfl)

private theorem PlaneDegree.form_add_det (x y : PlaneDegree w) :
    E.form y.vec (PlaneDegree.add y x).vec = (y.det x : ℚ) := by
  rw [PlaneDegree.add_vec, Submodule.coe_add, map_add, E.form_self, zero_add,
    PlaneDegree.form_det]

/-- **The pentagon exchange.** If `{y, x} = 1`, then `Ψ[x] Ψ[y] = Ψ[y] Ψ[y + x] Ψ[x]` for the
unit factors, and `y + x` lies in the open quadrant. -/
private theorem exists_exchange_of_det_eq_one (x y : PlaneDegree w) (h : y.det x = 1) :
    ∃ m : PlaneDegree w, x.deg < m.deg ∧ y.deg < m.deg ∧ ¬ m.Boundary ∧
      unitFactor x * unitFactor y = unitFactor y * unitFactor m * unitFactor x := by
  have hdetQ : (y.det x : ℚ) = 1 := by exact_mod_cast h
  obtain ⟨hy1, hx2⟩ := PlaneDegree.one_le_fst_and_one_le_snd (x := y) (y := x) (by omega)
  have hκx : rayIndex x.vec = 1 :=
    rayIndex_eq_one_of_form_eq_one y.vec (by rw [PlaneDegree.form_det, hdetQ])
  have hκy : rayIndex y.vec = 1 :=
    rayIndex_eq_one_of_form_eq_one (-x.vec) (by rw [PlaneDegree.form_neg_det, hdetQ])
  have hκm : rayIndex (PlaneDegree.add y x).vec = 1 :=
    rayIndex_eq_one_of_form_eq_one y.vec (by rw [PlaneDegree.form_add_det, hdetQ])
  refine ⟨PlaneDegree.add y x, ?_, ?_, ?_, ?_⟩
  · rw [PlaneDegree.deg_add]; have := y.deg_pos; omega
  · rw [PlaneDegree.deg_add]; have := x.deg_pos; omega
  · rw [PlaneDegree.boundary_iff]
    simp only [PlaneDegree.add_fst, PlaneDegree.add_snd]
    have := y.snd_nonneg
    have := x.fst_nonneg
    omega
  · rw [unitFactor_eq_dilogElement x hκx, unitFactor_eq_dilogElement y hκy,
      unitFactor_eq_dilogElement (PlaneDegree.add y x) hκm]
    exact Mei.SkewLieAlgebra.dilogElement_pentagon β hβ (plane w) y.mem x.mem y.ne_zero
      x.ne_zero (by rw [PlaneDegree.coefficientForm_det, hdetQ])

/-- The ordering algorithm in the rescaled plane, applied to `Ψ[e₂]^A Ψ[e₁]^B`, produces
`Ψ[e₁]^B Ψ[I] Ψ[e₂]^A` for an ordered list `I` of degrees of the open quadrant. -/
private theorem exists_isChain_rebase (k A B : ℕ) (x y : PlaneDegree w) (hk : x.deg + y.deg ≤ k)
    (IH : ∀ x' y' : PlaneDegree (Weight.rebase x y), PlaneDegree.Inverted x' y' →
      x'.deg + y'.deg ≤ k →
      ∃ M : List (PlaneDegree (Weight.rebase x y)),
        (∀ m ∈ M, x'.deg < m.deg ∧ y'.deg < m.deg ∧ ¬ m.Boundary) ∧
        CompletedGroup.projection k (unitFactor x' * unitFactor y') =
          CompletedGroup.projection k (unitFactor y' * (M.map unitFactor).prod * unitFactor x')) :
    ∃ I : List (PlaneDegree (Weight.rebase x y)), (∀ i ∈ I, ¬ i.Boundary) ∧
      (I.IsChain fun a b => ¬ PlaneDegree.Inverted a b) ∧
      CompletedGroup.projection k
          ((List.replicate A (PlaneDegree.e₂ (Weight.rebase x y)) ++
            List.replicate B (PlaneDegree.e₁ (Weight.rebase x y))).map unitFactor).prod =
        CompletedGroup.projection k
          ((List.replicate B (PlaneDegree.e₁ (Weight.rebase x y)) ++ I ++
            List.replicate A (PlaneDegree.e₂ (Weight.rebase x y))).map unitFactor).prod := by
  classical
  obtain ⟨l', hchain, -, hprod, hperm⟩ :=
    Mei.PositiveDegrees.exists_isChain_projection_prod_eq_of_exchange
      (plane (Weight.rebase x y))
      (SkewLieAlgebra.positiveGrading β hβ (plane (Weight.rebase x y)))
      ((List.replicate A (PlaneDegree.e₂ (Weight.rebase x y))) ++
        (List.replicate B (PlaneDegree.e₁ (Weight.rebase x y))))
      unitFactor PlaneDegree.deg PlaneDegree.Inverted PlaneDegree.Boundary k
      (fun m => unitFactor_mem_degreeFiltration m) (fun _ _ => PlaneDegree.Inverted.not_symm) IH
  have hW : (((List.replicate A (PlaneDegree.e₂ (Weight.rebase x y))) ++
      (List.replicate B (PlaneDegree.e₁ (Weight.rebase x y)))).filter
        fun m => decide (m.deg ≤ k)).filter (fun m => decide m.Boundary) =
        (List.replicate A (PlaneDegree.e₂ (Weight.rebase x y))) ++
          (List.replicate B (PlaneDegree.e₁ (Weight.rebase x y))) := by
    have := x.deg_pos
    have := y.deg_pos
    rw [List.filter_eq_self.mpr, List.filter_eq_self.mpr]
    · intro m hm
      simp only [List.mem_append, List.mem_replicate] at hm
      rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [decide_eq_true_eq, PlaneDegree.deg_e₂, Weight.snd_rebase]
        omega
      · simp only [decide_eq_true_eq, PlaneDegree.deg_e₁, Weight.fst_rebase]
        omega
    · intro m hm
      simp only [List.mem_filter, List.mem_append, List.mem_replicate] at hm
      rcases hm with ⟨⟨-, rfl⟩ | ⟨-, rfl⟩, -⟩ <;> simp [PlaneDegree.boundary_iff]
  obtain ⟨I, hl', hI⟩ := exists_eq_append_of_isChain A B l' hchain (by rwa [hW] at hperm)
  refine ⟨I, hI, hchain.infix ?_, ?_⟩
  · rw [hl']
    exact ⟨List.replicate B (PlaneDegree.e₁ _), List.replicate A (PlaneDegree.e₂ _), by simp⟩
  · rw [← hl']
    exact hprod.symm

/-- Carrying the identity of `exists_isChain_rebase` to the plane gives
`Ψ[x] Ψ[y] = Ψ[y] (∏ Ψ[T i]^{κ(i)/D}) Ψ[x]` at order `k`, because `Ψ[e₂]^A` and `Ψ[e₁]^B` are
carried to the unit factors of `x` and `y`. -/
private theorem projection_mul_eq_of_rebase (k A B : ℕ) (x y : PlaneDegree w)
    (hD : y.det x ≠ 0)
    (hAx : (A : ℚ) * (y.det x : ℚ)⁻¹ = rayIndex x.vec)
    (hBy : (B : ℚ) * (y.det x : ℚ)⁻¹ = rayIndex y.vec)
    (I : List (PlaneDegree (Weight.rebase x y)))
    (h : CompletedGroup.projection k
        ((List.replicate A (PlaneDegree.e₂ (Weight.rebase x y)) ++
          List.replicate B (PlaneDegree.e₁ (Weight.rebase x y))).map unitFactor).prod =
      CompletedGroup.projection k
        ((List.replicate B (PlaneDegree.e₁ (Weight.rebase x y)) ++ I ++
          List.replicate A (PlaneDegree.e₂ (Weight.rebase x y))).map unitFactor).prod) :
    CompletedGroup.projection k (unitFactor x * unitFactor y) =
      CompletedGroup.projection k (unitFactor y * ((I.map fun m =>
        dilogPow (rebasePos x y m) ((y.det x : ℚ)⁻¹ * rayIndex m.vec)).prod *
          unitFactor x)) := by
  have hT := projection_prod_rebasePos_eq x y hD k h
  set f : PlaneDegree (Weight.rebase x y) → Label w := fun m =>
    dilogPow (rebasePos x y m) ((y.det x : ℚ)⁻¹ * rayIndex m.vec) with hf
  have hfx : (f (PlaneDegree.e₂ (Weight.rebase x y))) ^ A = unitFactor x := by
    rw [hf]
    simp only [rebasePos_e₂, rayIndex_e₂, mul_one, ← dilogPow_natCast_mul, unitFactor_def, hAx]
  have hfy : (f (PlaneDegree.e₁ (Weight.rebase x y))) ^ B = unitFactor y := by
    rw [hf]
    simp only [rebasePos_e₁, rayIndex_e₁, mul_one, ← dilogPow_natCast_mul, unitFactor_def, hBy]
  simpa only [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, hfx,
    hfy, mul_assoc] using hT

/-- When `{y, x} > 0` the rescaling carries the open quadrant into the open quadrant, strictly
increasing the degree beyond those of `x` and `y`. -/
private theorem rebasePos_interior (x y : PlaneDegree w) (hdet : 0 < y.det x)
    (i : PlaneDegree (Weight.rebase x y)) (hi : ¬ i.Boundary) :
    x.deg < (rebasePos x y i).deg ∧ y.deg < (rebasePos x y i).deg ∧
      ¬ (rebasePos x y i).Boundary := by
  rw [PlaneDegree.boundary_iff] at hi
  push Not at hi
  have hi1 : 1 ≤ i.fst := by have := i.fst_nonneg; omega
  have hi2 : 1 ≤ i.snd := by have := i.snd_nonneg; omega
  obtain ⟨hy1, hx2⟩ := PlaneDegree.one_le_fst_and_one_le_snd hdet
  have hdegi : (i.deg : ℤ) = y.deg * i.fst + x.deg * i.snd := by
    rw [PlaneDegree.deg_eq, Weight.fst_rebase, Weight.snd_rebase]
  have hxd : (0 : ℤ) < x.deg := by exact_mod_cast x.deg_pos
  have hyd : (0 : ℤ) < y.deg := by exact_mod_cast y.deg_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [deg_rebasePos x y]
    have : (x.deg : ℤ) < i.deg := by rw [hdegi]; nlinarith
    exact_mod_cast this
  · rw [deg_rebasePos x y]
    have : (y.deg : ℤ) < i.deg := by rw [hdegi]; nlinarith
    exact_mod_cast this
  · rw [PlaneDegree.boundary_iff]
    rw [rebasePos_fst, rebasePos_snd]
    have := x.fst_nonneg
    have := y.snd_nonneg
    push Not
    constructor <;> nlinarith

/-- The middle factors `Ψ[T i]^{κ(i) / D}` of the exchange regroup into unit factors of the
plane. -/
private theorem exists_units_prod_eq_rebase (k : ℕ) (x y : PlaneDegree w)
    (hdet : 0 < y.det x)
    (I : List (PlaneDegree (Weight.rebase x y)))
    (hchain : I.IsChain fun a b => ¬ PlaneDegree.Inverted a b)
    (hmid : CompletedGroup.projection k
      ((unitFactor y)⁻¹ * unitFactor x * unitFactor y * (unitFactor x)⁻¹) =
      CompletedGroup.projection k (I.map fun m =>
        dilogPow (rebasePos x y m) ((y.det x : ℚ)⁻¹ * rayIndex m.vec)).prod) :
    ∃ M : List (PlaneDegree w), (∀ m ∈ M, ∃ i ∈ I, rebasePos x y i = m) ∧
      CompletedGroup.projection k (M.map unitFactor).prod =
        CompletedGroup.projection k (I.map fun m =>
          dilogPow (rebasePos x y m) ((y.det x : ℚ)⁻¹ * rayIndex m.vec)).prod := by
  classical
  have hDpos : 0 < (y.det x : ℚ) := by exact_mod_cast hdet
  have hDinv : 0 < (y.det x : ℚ)⁻¹ := inv_pos.mpr hDpos
  have hg : E.IsIntegralLabel (plane w)
      ((unitFactor y)⁻¹ * unitFactor x * unitFactor y * (unitFactor x)⁻¹) :=
    (((isIntegralLabel_unitFactor_inv y).mul E (plane w) (isIntegralLabel_unitFactor x)).mul E
      (plane w) (isIntegralLabel_unitFactor y)).mul E (plane w) (isIntegralLabel_unitFactor_inv x)
  have hcpos : ∀ i ∈ I, 0 < (y.det x : ℚ)⁻¹ * rayIndex i.vec := fun i _ =>
    mul_pos hDinv i.rayIndex_pos
  have hxy : ∀ i ∈ I, (rebasePos x y i).vec ∈ AddSubmonoid.closure {x.vec, y.vec} := by
    intro i _
    refine (AddSubmonoid.mem_closure_pair x.vec y.vec _).mpr ⟨i.snd.toNat, i.fst.toNat, ?_⟩
    refine Subtype.ext (Prod.ext ?_ ?_) <;>
      simp [Int.toNat_of_nonneg i.fst_nonneg, Int.toNat_of_nonneg i.snd_nonneg, mul_comm,
        add_comm]
  have hIchain : I.IsChain fun i j => 0 ≤ E.coefficientForm ℚ (rebasePos x y i).vec
      (rebasePos x y j).vec := by
    refine hchain.imp (fun a b hab => ?_)
    rw [rebasePos_vec, rebasePos_vec, form_rebase]
    exact mul_nonneg hDpos.le
      (not_lt.mp (mt (PlaneDegree.inverted_iff_coefficientForm_lt a b).mpr hab))
  exact (exists_units_prod_eq_of_isChain I (rebasePos x y)
    (fun i => (y.det x : ℚ)⁻¹ * rayIndex i.vec) hcpos x y hxy hIchain hg (k := k) hmid).imp
      fun M hM => ⟨hM.1, hM.2.trans hmid⟩

/-- For a plane degree `x`, a vector `a` and `D > 0` with `{a, x} = D`, the ray index of `x` is
`A / D` for some natural number `A`. -/
private theorem exists_nat_mul_inv_eq_rayIndex (x : PlaneDegree w) (a : ℤ × ℤ) {D : ℚ}
    (hD : 0 < D) (hform : E.form a x.vec = D) : ∃ A : ℕ, (A : ℚ) * D⁻¹ = rayIndex x.vec := by
  obtain ⟨z, hz⟩ := E.exists_int_eq_rayIndex_mul_form x.vec.property a
  rw [hform] at hz
  have hzpos : 0 < z := by
    have : (0 : ℚ) < z := by rw [← hz]; exact mul_pos x.rayIndex_pos hD
    exact_mod_cast this
  obtain ⟨A, rfl⟩ : ∃ A : ℕ, (A : ℤ) = z := ⟨z.toNat, Int.toNat_of_nonneg hzpos.le⟩
  refine ⟨A, ?_⟩
  push_cast at hz
  rw [← hz]
  field_simp

/-- Conjugating the exchange `X Y = Y T X` gives `Y⁻¹ X Y X⁻¹ = T`. -/
private theorem conj_eq_of_mul_eq {G : Type*} [Group G] {X Y T : G} (h : X * Y = Y * (T * X)) :
    Y⁻¹ * X * Y * X⁻¹ = T := by
  calc Y⁻¹ * X * Y * X⁻¹ = Y⁻¹ * (X * Y) * X⁻¹ := by group
    _ = T := by rw [h]; group

/-- The recursive step of the exchange: for `{y, x} ≥ 2` the exchange of the unit factors of `x`
and `y` follows from the exchanges in the plane rescaled along `x, y`. -/
private theorem exists_exchange_of_two_le_det (k : ℕ) (x y : PlaneDegree w)
    (hdet : 2 ≤ y.det x) (hk : x.deg + y.deg ≤ k)
    (IH : ∀ x' y' : PlaneDegree (Weight.rebase x y), PlaneDegree.Inverted x' y' →
      x'.deg + y'.deg ≤ k →
      ∃ M : List (PlaneDegree (Weight.rebase x y)),
        (∀ m ∈ M, x'.deg < m.deg ∧ y'.deg < m.deg ∧ ¬ m.Boundary) ∧
        CompletedGroup.projection k (unitFactor x' * unitFactor y') =
          CompletedGroup.projection k (unitFactor y' * (M.map unitFactor).prod * unitFactor x')) :
    ∃ M : List (PlaneDegree w), (∀ m ∈ M, x.deg < m.deg ∧ y.deg < m.deg ∧ ¬ m.Boundary) ∧
      CompletedGroup.projection k (unitFactor x * unitFactor y) =
        CompletedGroup.projection k (unitFactor y * (M.map unitFactor).prod * unitFactor x) := by
  have hdet0 : 0 < y.det x := by omega
  have hDpos : 0 < (y.det x : ℚ) := by exact_mod_cast hdet0
  have hD : y.det x ≠ 0 := hdet0.ne'
  -- The unit factors of `x` and `y` are powers `Ψ[x]^{A/D}`, `Ψ[y]^{B/D}`.
  obtain ⟨A, hAx⟩ := exists_nat_mul_inv_eq_rayIndex x (y.vec : ℤ × ℤ) hDpos
    (PlaneDegree.form_det y x)
  obtain ⟨B, hBy⟩ := exists_nat_mul_inv_eq_rayIndex y (-(x.vec : ℤ × ℤ)) hDpos (by
    rw [map_neg, LinearMap.neg_apply, E.form_swap, neg_neg]
    exact PlaneDegree.form_det y x)
  obtain ⟨I, hI, hchain, hprod⟩ := exists_isChain_rebase k A B x y hk IH
  have hT := projection_mul_eq_of_rebase k A B x y hD hAx hBy I hprod
  have hmid : CompletedGroup.projection k
      ((unitFactor y)⁻¹ * unitFactor x * unitFactor y * (unitFactor x)⁻¹) =
      CompletedGroup.projection k (I.map fun m =>
        dilogPow (rebasePos x y m) ((y.det x : ℚ)⁻¹ * rayIndex m.vec)).prod := by
    simp only [map_mul, map_inv]
    exact conj_eq_of_mul_eq (by simpa only [map_mul] using hT)
  obtain ⟨M, hMmem, hMprod⟩ := exists_units_prod_eq_rebase k x y hdet0 I hchain hmid
  refine ⟨M, fun m hm => ?_, ?_⟩
  · obtain ⟨i, hiI, rfl⟩ := hMmem m hm
    exact rebasePos_interior x y hdet0 i (hI i hiI)
  · rw [hT]
    simp only [map_mul]
    rw [hMprod, mul_assoc]

/-- The rescaled plane has strictly larger weights when `{y, x} ≥ 2`. -/
private theorem fst_add_snd_lt_deg_add_deg (x y : PlaneDegree w) (hdet : 2 ≤ y.det x) :
    w.fst + w.snd < x.deg + y.deg := by
  obtain ⟨hy1, hx2⟩ := PlaneDegree.one_le_fst_and_one_le_snd (x := y) (y := x) (by omega)
  have hdet' : y.fst * x.snd - y.snd * x.fst ≥ 2 := by rwa [PlaneDegree.det_eq] at hdet
  have h1 := y.fst_nonneg
  have h2 := x.snd_nonneg
  have h3 := x.fst_nonneg
  have h4 := y.snd_nonneg
  have hw1 : (0 : ℤ) < w.fst := by exact_mod_cast w.fst_pos
  have hw2 : (0 : ℤ) < w.snd := by exact_mod_cast w.snd_pos
  have hsum : ((x.deg + y.deg : ℕ) : ℤ) = w.fst * (x.fst + y.fst) + w.snd * (x.snd + y.snd) := by
    push_cast
    rw [PlaneDegree.deg_eq, PlaneDegree.deg_eq]
    ring
  have : ((w.fst + w.snd : ℕ) : ℤ) < ((x.deg + y.deg : ℕ) : ℤ) := by
    rw [hsum]
    push_cast
    by_cases hc : 2 ≤ x.fst + y.fst
    · nlinarith
    · have hy : y.fst = 1 := by omega
      have hx : x.fst = 0 := by omega
      rw [hy, hx] at hdet'
      have : 2 ≤ x.snd + y.snd := by omega
      nlinarith
  exact_mod_cast this

/-- **Exchange of antiordered unit factors.** For nonzero plane degrees `x, y` with
`{x, y} < 0`, the product of the unit factors `Ψ[x]^{κ(x)} Ψ[y]^{κ(y)}` equals, at order `k`,
`Ψ[y]^{κ(y)} M Ψ[x]^{κ(x)}` for a product `M` of unit factors of degrees in the open
quadrant and of weighted degree larger than those of `x` and `y`. -/
theorem exists_exchange (k : ℕ) {w : Weight} (x y : PlaneDegree w)
    (hxy : PlaneDegree.Inverted x y) (hk : x.deg + y.deg ≤ k) :
    ∃ M : List (PlaneDegree w), (∀ m ∈ M, x.deg < m.deg ∧ y.deg < m.deg ∧ ¬ m.Boundary) ∧
      CompletedGroup.projection k (unitFactor x * unitFactor y) =
        CompletedGroup.projection k (unitFactor y * (M.map unitFactor).prod * unitFactor x) := by
  suffices key : ∀ n : ℕ, ∀ (w : Weight) (x y : PlaneDegree w), k + 1 - (w.fst + w.snd) = n →
      PlaneDegree.Inverted x y → x.deg + y.deg ≤ k → ∃ M : List (PlaneDegree w),
        (∀ m ∈ M, x.deg < m.deg ∧ y.deg < m.deg ∧ ¬ m.Boundary) ∧
          CompletedGroup.projection k (unitFactor x * unitFactor y) =
            CompletedGroup.projection k (unitFactor y * (M.map unitFactor).prod * unitFactor x) from
    key _ w x y rfl hxy hk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w x y hn hbad hk
  have hdet0 : 0 < y.det x := by
    have := (PlaneDegree.inverted_iff_det_neg x y).mp hbad
    simp only [PlaneDegree.det_eq] at this ⊢
    linarith
  by_cases h1 : y.det x = 1
  · obtain ⟨m, hm1, hm2, hm3, hm4⟩ := exists_exchange_of_det_eq_one x y h1
    refine ⟨[m], fun m' hm' => ?_, ?_⟩
    · rw [List.mem_singleton] at hm'
      subst hm'
      exact ⟨hm1, hm2, hm3⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hm4]
  · have hdet : 2 ≤ y.det x := by omega
    have hlt := fst_add_snd_lt_deg_add_deg x y hdet
    refine exists_exchange_of_two_le_det k x y hdet hk fun x' y' hb hk' => ?_
    refine ih (k + 1 - ((Weight.rebase x y).fst + (Weight.rebase x y).snd)) ?_
      (Weight.rebase x y) x' y' rfl hb hk'
    rw [Weight.fst_rebase, Weight.snd_rebase]
    omega

end Mei.StandardPlane
