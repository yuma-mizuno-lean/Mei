/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.Finite

/-!
# Path products from local crossing formulas

Let `F` be a function on the ambient space with values in the label group of a finite
wall diagram. Suppose that `F` is locally constant off the walls, and that every regular
point of a wall `P` has a neighbourhood in which each admissible segment crossing `P`
has product `F y * (F x)⁻¹`, where `x` and `y` are its endpoints. Then every admissible
path from `x` to `y` has product `F y * (F x)⁻¹`. In particular the diagram is consistent.

This is the local-to-global step of consistency proofs for diagrams built from pointwise
data, such as Bridgeland's reconstruction of a scattering diagram from the sign factors
of a group element: Tom Bridgeland, *Scattering diagrams, Hall algebras and stability
conditions*, [arXiv:1603.00416](https://arxiv.org/abs/1603.00416), §3.4.

Along a segment, the crossings occur at finitely many parameters. The proof isolates the
first remaining crossing in a short subsegment, inside the neighbourhood supplied for its
crossing point, and inducts on the number of crossings left. The pieces between
crossings meet no wall, so `F` is constant on them by connectedness of the unit interval.
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V H : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : FinitePolyhedralComplex h} [Group H] (D : FiniteWallDiagram C H) {F : V → H}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- If `F` is locally constant off the walls and computes the product of every short
admissible segment crossing a wall near a regular point, then it computes the product of
every admissible segment. -/
theorem pathProduct_toPath_eq_mul_inv_of_local
    (hF : ∀ θ, (∀ P : C.walls, θ ∉ (P : Set V)) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ (P : C.walls) (θ : V), θ ∈ (P : Set V) →
      θ ∉ singularSupport (fun Q : C.walls => (Q : Set V)) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ (x y : WallComplement (fun Q : C.walls => (Q : Set V)))
        (e : x ⟶ y), dist x.val θ < ε → dist y.val θ < ε →
        (∃ t, (P, t) ∈ WallComplement.crossings x y) →
        D.pathProduct e.toPath = F y.val * (F x.val)⁻¹)
    (e : x ⟶ y) : D.pathProduct e.toPath = F y.val * (F x.val)⁻¹ := by
  classical
  let γ : ℝ → V := AffineMap.lineMap x.val y.val
  have hγ (s u r : ℝ) : AffineMap.lineMap (γ s) (γ u) r = γ (s + r * (u - s)) := by
    simp only [γ, AffineMap.lineMap_apply_module']
    module
  have hy : y.val = γ 1 := (AffineMap.lineMap_apply_one _ _).symm
  have hI₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- The finitely many crossing parameters of the segment.
  let T : Set ℝ := Prod.snd '' WallComplement.crossings x y
  have hT : T.Finite := e.down.finite_crossings.image _
  have hoff {r : ℝ} (hrT : r ∉ T) (hr : r ∈ Icc (0 : ℝ) 1) (Q : C.walls) :
      γ r ∉ (Q : Set V) := fun hQ =>
    hrT ⟨(Q, r), (WallComplement.mem_crossings _ _ _ _).mpr ⟨hr, hQ⟩, rfl⟩
  -- Splitting a segment at an interior parameter multiplies the two products.
  have hsplit {a b c : WallComplement (fun P : C.walls => (P : Set V))}
      (e₀ : a ⟶ b) (e₁ : a ⟶ c) (e₂ : c ⟶ b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
      (hc : c.val = AffineMap.lineMap a.val b.val t) :
      D.pathProduct e₀.toPath = D.pathProduct e₂.toPath * D.pathProduct e₁.toPath := by
    rw [← D.pathProduct_eq_of_isSubdivision (Quiver.Path.IsSubdivision.split e₀ e₁ e₂ ht hc),
      pathProduct_comp]
  -- Induct on the number of crossings after the starting parameter `s`.
  have key : ∀ (n : ℕ) (s : ℝ) (a : WallComplement (fun P : C.walls => (P : Set V))),
      (T ∩ Ioc s 1).ncard = n → s ∈ Icc (0 : ℝ) 1 → a.val = γ s → ∀ e' : a ⟶ y,
        D.pathProduct e'.toPath = F y.val * (F a.val)⁻¹ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro s a hn hs ha e'
    rcases (T ∩ Ioc s 1).eq_empty_or_nonempty with hempty | hne
    · -- No crossing remains: the product is trivial and `F` is constant.
      have hcr : WallComplement.crossings a y = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun ⟨Q, r⟩ hr => ?_
        obtain ⟨⟨hr₀, hr₁⟩, hQ⟩ :=
          (WallComplement.mem_crossings_subsegment hs hI₁ ha hy Q r).mp hr
        rcases eq_or_lt_of_le (le_add_of_nonneg_right (mul_nonneg hr₀ (sub_nonneg.mpr hs.2)) :
            s ≤ s + r * (1 - s)) with hr' | hr'
        · exact a.notMem Q
            (by rw [ha, hr']; exact ((WallComplement.mem_crossings _ _ _ _).mp hQ).2)
        · exact (eq_empty_iff_forall_notMem.mp hempty) _
            ⟨⟨_, hQ, rfl⟩, hr', ((WallComplement.mem_crossings _ _ _ _).mp hQ).1.2⟩
      rw [D.pathProduct_toPath_eq_one e' hcr,
        WallComplement.apply_eq_of_crossings_eq_empty hF hcr, mul_inv_cancel]
    · -- Isolate the first remaining crossing parameter `t`, on the wall `P`.
      obtain ⟨t₀, ⟨ht₀T, ht₀s, -⟩, hmin⟩ := exists_min_image _ id (hT.inter_of_left _) hne
      obtain ⟨⟨P, t⟩, hPt, rfl : t = t₀⟩ := ht₀T
      obtain ⟨ht₀I, hθP⟩ := (WallComplement.mem_crossings _ _ _ _).mp hPt
      have ht₀1 : t < 1 := (e.down.crossing_mem_intrinsicInterior ht₀I hθP).1.2
      obtain ⟨ε, hε, hloc⟩ := hcross P (γ t) hθP (e.down.regular t ht₀I)
      obtain ⟨τ₁, hτ₁, hγτ⟩ := Metric.continuous_iff.mp
        (AffineMap.lineMap_continuous (p := x.val) (q := y.val)) t ε hε
      obtain ⟨τ₂, hτ₂, hball⟩ := Metric.mem_nhds_iff.mp
        ((hT.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds
          (by simp : t ∉ T \ {t}))
      -- Cut at `t ± m / 2`, within `τ₁` and `τ₂` of `t` and inside `(s, 1)`.
      set m := min (min τ₁ τ₂) (min (t - s) (1 - t))
      have hm : 0 < m := lt_min (lt_min hτ₁ hτ₂) (lt_min (sub_pos.mpr ht₀s) (sub_pos.mpr ht₀1))
      have hm₁ : m ≤ τ₁ := (min_le_left _ _).trans (min_le_left _ _)
      have hm₂ : m ≤ τ₂ := (min_le_left _ _).trans (min_le_right _ _)
      have hm₃ : m ≤ t - s := (min_le_right _ _).trans (min_le_left _ _)
      have hm₄ : m ≤ 1 - t := (min_le_right _ _).trans (min_le_right _ _)
      have hnear {r : ℝ} (hr : |r - t| ≤ m / 2) : dist r t < τ₁ ∧ dist r t < τ₂ := by
        rw [Real.dist_eq]
        constructor <;> linarith
      have hnotT {r : ℝ} (hr : |r - t| ≤ m / 2) (hrt : r ≠ t) : r ∉ T := fun hrT =>
        hball (hnear hr).2 ⟨hrT, hrt⟩
      have hs₁ : |t - m / 2 - t| ≤ m / 2 := by
        rw [abs_le]
        constructor <;> linarith
      have hs₂ : |t + m / 2 - t| ≤ m / 2 := by
        rw [abs_le]
        constructor <;> linarith
      have hs₁I : t - m / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith⟩
      have hs₂I : t + m / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith⟩
      let a₁ : WallComplement (fun P : C.walls => (P : Set V)) :=
        ⟨γ (t - m / 2), hoff (hnotT hs₁ (by linarith)) hs₁I⟩
      let a₂ : WallComplement (fun P : C.walls => (P : Set V)) :=
        ⟨γ (t + m / 2), hoff (hnotT hs₂ (by linarith)) hs₂I⟩
      let e₁ : a ⟶ a₁ := ⟨e.down.subsegment hs hs₁I ha rfl⟩
      let e₂ : a₁ ⟶ a₂ := ⟨e.down.subsegment hs₁I hs₂I rfl rfl⟩
      let e₃ : a₂ ⟶ y := ⟨e.down.subsegment hs₂I hI₁ rfl hy⟩
      let e₂₃ : a₁ ⟶ y := ⟨e.down.subsegment hs₁I hI₁ rfl hy⟩
      have hprod : D.pathProduct e'.toPath =
          D.pathProduct e₃.toPath * D.pathProduct e₂.toPath * D.pathProduct e₁.toPath := by
        have hsm : 0 < 1 - s := by linarith
        have hsm' : 0 < 1 - (t - m / 2) := by linarith
        have hp₁ : s + (t - m / 2 - s) / (1 - s) * (1 - s) = t - m / 2 := by
          rw [div_mul_cancel₀ _ hsm.ne']
          ring
        have hp₂ : t - m / 2 + m / (1 - (t - m / 2)) * (1 - (t - m / 2)) = t + m / 2 := by
          rw [div_mul_cancel₀ _ hsm'.ne']
          ring
        rw [hsplit e' e₁ e₂₃ (t := (t - m / 2 - s) / (1 - s))
            ⟨div_pos (by linarith) hsm, (div_lt_one hsm).mpr (by linarith)⟩
            (by rw [ha, hy, hγ, hp₁]),
          hsplit e₂₃ e₂ e₃ (t := m / (1 - (t - m / 2)))
            ⟨div_pos hm hsm', (div_lt_one hsm').mpr (by linarith)⟩
            (by rw [hy]; exact (congrArg γ hp₂).symm.trans (hγ _ _ _).symm)]
      -- Before the isolated crossing the segment meets no wall.
      have hcr₁ : WallComplement.crossings a a₁ = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun ⟨Q, r⟩ hr => ?_
        obtain ⟨⟨hr₀, hr₁⟩, hQ⟩ :=
          (WallComplement.mem_crossings_subsegment hs hs₁I ha rfl Q r).mp hr
        have hle : s + r * (t - m / 2 - s) ≤ t - m / 2 := by nlinarith
        rcases eq_or_lt_of_le (le_add_of_nonneg_right
            (mul_nonneg hr₀ (by linarith : (0 : ℝ) ≤ t - m / 2 - s)) :
            s ≤ s + r * (t - m / 2 - s)) with hr' | hr'
        · exact a.notMem Q
            (by rw [ha, hr']; exact ((WallComplement.mem_crossings _ _ _ _).mp hQ).2)
        · have := hmin _ ⟨⟨_, hQ, rfl⟩, hr', by linarith⟩
          simp only [id] at this
          linarith
      -- The isolated crossing is computed by the local formula.
      have hcr₂ : (P, (1 / 2 : ℝ)) ∈ WallComplement.crossings a₁ a₂ := by
        rw [WallComplement.mem_crossings_subsegment hs₁I hs₂I rfl rfl]
        refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
        convert hPt using 2
        ring
      have hd₁ : dist a₁.val (γ t) < ε := hγτ _ (hnear hs₁).1
      have hd₂ : dist a₂.val (γ t) < ε := hγτ _ (hnear hs₂).1
      -- After it, one crossing fewer remains.
      have hlt : (T ∩ Ioc (t + m / 2) 1).ncard < n := by
        rw [← hn]
        refine ncard_lt_ncard ?_ (hT.inter_of_left _)
        refine LE.le.ssubset_of_not_superset
          (fun r hr => ⟨hr.1, by linarith [hr.2.1], hr.2.2⟩) fun hsub => ?_
        have := (hsub ⟨⟨(P, t), hPt, rfl⟩, ht₀s, ht₀I.2⟩).2.1
        linarith
      rw [hprod, ih _ hlt (t + m / 2) a₂ rfl hs₂I rfl e₃,
        hloc a₁ a₂ e₂ hd₁ hd₂ ⟨_, hcr₂⟩, D.pathProduct_toPath_eq_one e₁ hcr₁,
        WallComplement.apply_eq_of_crossings_eq_empty hF hcr₁]
      group
  exact key _ 0 x rfl ⟨le_rfl, zero_le_one⟩ (AffineMap.lineMap_apply_zero _ _).symm e

/-- If `F` is locally constant off the walls and computes the product of every short
admissible segment crossing a wall near a regular point, then every admissible path from
`x` to `y` has product `F y * (F x)⁻¹`. -/
theorem pathProduct_eq_mul_inv_of_local
    (hF : ∀ θ, (∀ P : C.walls, θ ∉ (P : Set V)) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ (P : C.walls) (θ : V), θ ∈ (P : Set V) →
      θ ∉ singularSupport (fun Q : C.walls => (Q : Set V)) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ (x y : WallComplement (fun Q : C.walls => (Q : Set V)))
        (e : x ⟶ y), dist x.val θ < ε → dist y.val θ < ε →
        (∃ t, (P, t) ∈ WallComplement.crossings x y) →
        D.pathProduct e.toPath = F y.val * (F x.val)⁻¹)
    (p : AdmissiblePLPath x y) : D.pathProduct p = F y.val * (F x.val)⁻¹ := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [pathProduct_cons, D.pathProduct_toPath_eq_mul_inv_of_local hF hcross e, ih]
    group

/-- A diagram whose single crossings near regular wall points are computed by a function
locally constant off the walls is consistent. -/
theorem consistent_of_local
    (hF : ∀ θ, (∀ P : C.walls, θ ∉ (P : Set V)) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ (P : C.walls) (θ : V), θ ∈ (P : Set V) →
      θ ∉ singularSupport (fun Q : C.walls => (Q : Set V)) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ (x y : WallComplement (fun Q : C.walls => (Q : Set V)))
        (e : x ⟶ y), dist x.val θ < ε → dist y.val θ < ε →
        (∃ t, (P, t) ∈ WallComplement.crossings x y) →
        D.pathProduct e.toPath = F y.val * (F x.val)⁻¹) :
    D.Consistent := D.consistent_def.mpr fun _ _ p q => by
  rw [D.pathProduct_eq_mul_inv_of_local hF hcross p,
    D.pathProduct_eq_mul_inv_of_local hF hcross q]

end Mei.FiniteWallDiagram
