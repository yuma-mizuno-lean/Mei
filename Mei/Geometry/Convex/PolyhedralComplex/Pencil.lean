/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.Path.Hyperplane
public import Mei.LinearAlgebra.AffineSpace.Ordered
public import Mei.Algebra.Field.Basic

/-!
# Crossing words in a pencil of hyperplanes

Let `U` be a convex region missing the singular support of a finite polyhedral
complex, and `ℓ` an affine function positive on `U`. Suppose each wall meeting `U`
is cut out there by an affine function in the pencil spanned by `ℓ` and a second
affine function `m`. Within `U` the walls are then level sets of the slope `m / ℓ`.
The slope is monotone along every segment in `U`, so a segment crosses the walls
in the order of their slopes. Consequently admissible polygonal paths in `U` have
crossing words depending only on their endpoints, already in the free group on
the walls.

The word of a path from `x` to `y` is `T y * (T x)⁻¹`, where `T z` multiplies the
signed letters of the walls of slope below that of `z`, the largest slope on the
left. This is the situation in an open half-space bounded by a hyperplane through
a codimension-two joint, near that joint: the walls there are half-hyperplanes
bounded by the joint, so the walls met by the half-space form a pencil. Parallel
walls are the case of constant `ℓ`.

The crossing lists are identified using
`FinitePolyhedralComplex.orderedCrossings_eq_iff` and the hyperplane crossing
criterion `WallComplement.exists_crossing_iff_of_hyperplane`; sorted lists are
compared with Mathlib's `List.Pairwise.eq_of_mem_iff`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : FinitePolyhedralComplex h}

/-- The potential of a pencil: the signed letters of the listed walls of slope
below `s`, the largest slope on the left. -/
private def pencilPotential (L : List C.walls) (κ : C.walls → ℝ) (β : C.walls → ℝ) (s : ℝ) :
    FreeGroup C.walls :=
  ((L.filter fun P => κ P < s).reverse.map fun P =>
    if 0 < β P then (FreeGroup.of P)⁻¹ else FreeGroup.of P).prod

variable {ν : C.walls → V →ₗ[ℝ] ℝ} {b : C.walls → ℝ} {U : Set V} {ℓ m : V →ᵃ[ℝ] ℝ}
  {α β : C.walls → ℝ} {L : List C.walls}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- In the region, a wall meeting it is the level set of the slope `m / ℓ` at the
wall's slope `-α / β`. -/
private theorem mem_iff_div_eq_of_pencil (hℓ : ∀ z ∈ U, 0 < ℓ z)
    (hwall : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z ∈ U, z ∈ (P : Set V) ↔ ν P z = b P)
    (hpen : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z, ν P z - b P = α P * ℓ z + β P * m z)
    (hβ : ∀ P : C.walls, (U ∩ P).Nonempty → β P ≠ 0) {P : C.walls} (hP : (U ∩ P).Nonempty)
    {z : V} (hz : z ∈ U) : z ∈ (P : Set V) ↔ m z / ℓ z = -α P / β P := by
  rw [hwall P hP z hz, ← sub_eq_zero, hpen P hP z,
    mul_add_mul_eq_mul_mul_div_sub (hℓ z hz).ne' (hβ P hP)]
  simp [hβ P hP, (hℓ z hz).ne', sub_eq_zero]

/-- A segment in the region, traversed with nondecreasing slope, crosses exactly the
walls meeting the region whose slope lies strictly between the slopes of its ends. -/
private theorem exists_crossing_iff_of_pencil (hU : Convex ℝ U) (hℓ : ∀ z ∈ U, 0 < ℓ z)
    (hwall : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z ∈ U, z ∈ (P : Set V) ↔ ν P z = b P)
    (hpen : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z, ν P z - b P = α P * ℓ z + β P * m z)
    (hβ : ∀ P : C.walls, (U ∩ P).Nonempty → β P ≠ 0) (hx : x.val ∈ U) (hy : y.val ∈ U)
    (hxy : m x.val / ℓ x.val ≤ m y.val / ℓ y.val) (P : C.walls) :
    (∃ t, (P, t) ∈ WallComplement.crossings x y) ↔
      (U ∩ P).Nonempty ∧ m x.val / ℓ x.val < -α P / β P ∧ -α P / β P < m y.val / ℓ y.val := by
  set κ : C.walls → ℝ := fun P => -α P / β P with hκ
  have hmem := mem_iff_div_eq_of_pencil hℓ hwall hpen hβ (P := P)
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨htI, htP⟩ := (WallComplement.mem_crossings x y P t).mp ht
    have hP : (U ∩ P).Nonempty := ⟨_, hU.lineMap_mem hx hy htI, htP⟩
    have heq := (hmem hP (hU.lineMap_mem hx hy htI)).mp htP
    -- The slope is monotone along the segment and differs from `κ P` at both ends.
    have hmono := AffineMap.monotoneOn_div_lineMap ℓ m (hℓ _ hx) (hℓ _ hy) hxy
    have h0 := hmono (by simp) htI htI.1
    have h1 := hmono htI (by simp) htI.2
    simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, heq] at h0 h1
    exact ⟨hP, lt_of_le_of_ne h0 fun he => x.notMem P ((hmem hP hx).mpr he),
      lt_of_le_of_ne h1 fun he => y.notMem P ((hmem hP hy).mpr he.symm)⟩
  · rintro ⟨hP, hxP, hPy⟩
    -- The pencil function of the wall has opposite signs at the two ends.
    let f : V →ᵃ[ℝ] ℝ := (ν P).toAffineMap - AffineMap.const ℝ V (b P)
    have hf (z : V) : f z = ν P z - b P := by simp [f]
    have hc := WallComplement.exists_crossing_iff_of_hyperplane x y f (j := P)
      (fun z hz => (hwall P hP z (hU.segment_subset hx hy hz)).trans (by rw [hf, sub_eq_zero]))
    apply hc.mpr
    rw [hf, hf, hpen P hP x.val, mul_add_mul_eq_mul_mul_div_sub (hℓ _ hx).ne' (hβ P hP),
      hpen P hP y.val, mul_add_mul_eq_mul_mul_div_sub (hℓ _ hy).ne' (hβ P hP)]
    have hx' : m x.val / ℓ x.val - κ P < 0 := by linarith
    have hy' : 0 < m y.val / ℓ y.val - κ P := by linarith
    rcases lt_or_gt_of_ne (hβ P hP) with hb | hb
    · have h1 : 0 < β P * ℓ x.val * (m x.val / ℓ x.val - κ P) :=
        mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hb (hℓ _ hx)) hx'
      have h2 : β P * ℓ y.val * (m y.val / ℓ y.val - κ P) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hb (hℓ _ hy)) hy'
      simp [hκ] at h1 h2 ⊢
      simp [h1, h2.le.not_gt]
    · have h1 : β P * ℓ x.val * (m x.val / ℓ x.val - κ P) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hb (hℓ _ hx)) hx'
      have h2 : 0 < β P * ℓ y.val * (m y.val / ℓ y.val - κ P) :=
        mul_pos (mul_pos hb (hℓ _ hy)) hy'
      simp [hκ] at h1 h2 ⊢
      simp [h1.le.not_gt, h2]

/-- A segment in the region, traversed with nondecreasing slope, changes the
pencil potential by its crossing word. -/
private theorem segmentCrossingWord_eq_pencilPotential_of_le (hU : Convex ℝ U)
    (hℓ : ∀ z ∈ U, 0 < ℓ z)
    (hwall : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z ∈ U, z ∈ (P : Set V) ↔ ν P z = b P)
    (hpen : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z, ν P z - b P = α P * ℓ z + β P * m z)
    (hβ : ∀ P : C.walls, (U ∩ P).Nonempty → β P ≠ 0)
    (hL : L.Pairwise fun P Q => -α P / β P < -α Q / β Q)
    (hLmem : ∀ P, P ∈ L ↔ (U ∩ P).Nonempty)
    (e : x ⟶ y) (hx : x.val ∈ U) (hy : y.val ∈ U)
    (hxy : m x.val / ℓ x.val ≤ m y.val / ℓ y.val) :
    C.segmentCrossingWord ν e =
      pencilPotential L (fun P => -α P / β P) β (m y.val / ℓ y.val) *
        (pencilPotential L (fun P => -α P / β P) β (m x.val / ℓ x.val))⁻¹ := by
  classical
  set κ : C.walls → ℝ := fun P => -α P / β P with hκ
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : AffineMap.lineMap x.val y.val t ∈ U :=
    hU.lineMap_mem hx hy ht
  have hmem {P : C.walls} (hP : (U ∩ P).Nonempty) {z : V} (hz : z ∈ U) :
      z ∈ (P : Set V) ↔ m z / ℓ z = κ P :=
    mem_iff_div_eq_of_pencil hℓ hwall hpen hβ hP hz
  have hxκ (P : C.walls) (hP : P ∈ L) : m x.val / ℓ x.val ≠ κ P :=
    fun he => x.notMem P ((hmem ((hLmem P).mp hP) hx).mpr he)
  have hinj : L.Pairwise fun P Q => κ P ≠ κ Q := hL.imp ne_of_lt
  have : Std.Symm (fun P Q : C.walls => κ P ≠ κ Q) := ⟨fun _ _ h => Ne.symm h⟩
  have : Std.Antisymm (fun P Q : C.walls => κ P < κ Q) :=
    ⟨fun _ _ hab hba => (lt_asymm hab hba).elim⟩
  have : Std.Irrefl (fun P Q : C.walls => κ P < κ Q) := ⟨fun P => lt_irrefl (κ P)⟩
  -- In time order, the crossed walls are the listed walls of intermediate slope.
  have hfst : (C.orderedCrossings e).map Prod.fst =
      L.filter fun P => m x.val / ℓ x.val < κ P ∧ κ P < m y.val / ℓ y.val := by
    apply List.Pairwise.eq_of_mem_iff ?_ (hL.filter _)
    · intro P
      simp only [List.mem_map, mem_orderedCrossings, Prod.exists, exists_and_right,
        exists_eq_right, List.mem_filter, decide_eq_true_eq, hLmem]
      exact exists_crossing_iff_of_pencil hU hℓ hwall hpen hβ hx hy hxy P
    · apply List.pairwise_map.mpr
      refine (C.pairwise_orderedCrossings e).imp_of_mem fun {a a'} ha ha' hlt => ?_
      obtain ⟨haI, haP⟩ := (WallComplement.mem_crossings x y _ _).mp
        ((C.mem_orderedCrossings e a).mp ha)
      obtain ⟨haI', haP'⟩ := (WallComplement.mem_crossings x y _ _).mp
        ((C.mem_orderedCrossings e a').mp ha')
      have hP : (U ∩ a.1).Nonempty := ⟨_, hseg _ haI, haP⟩
      have hP' : (U ∩ a'.1).Nonempty := ⟨_, hseg _ haI', haP'⟩
      have hne : a.1 ≠ a'.1 := fun he => hlt.ne
        (e.down.subsingleton_crossing a.1 ⟨haI, haP⟩ ⟨haI', he ▸ haP'⟩)
      have hle := AffineMap.monotoneOn_div_lineMap ℓ m (hℓ _ hx) (hℓ _ hy) hxy haI haI' hlt.le
      dsimp only at hle
      rw [(hmem hP (hseg _ haI)).mp haP, (hmem hP' (hseg _ haI')).mp haP'] at hle
      exact lt_of_le_of_ne hle
        (hinj.forall ((hLmem _).mpr hP) ((hLmem _).mpr hP') hne)
  -- Each crossing letter is determined by the sign of the wall's `m`-coefficient.
  have hletter (P : C.walls)
      (hP : P ∈ L.filter fun P => m x.val / ℓ x.val < κ P ∧ κ P < m y.val / ℓ y.val) :
      C.crossingLetter ν x y P = if 0 < β P then (FreeGroup.of P)⁻¹ else FreeGroup.of P := by
    simp only [List.mem_filter, decide_eq_true_eq] at hP
    obtain ⟨hPL, hxP, hPy⟩ := hP
    have hPU := (hLmem P).mp hPL
    have hv : ν P (y.val - x.val) =
        β P * (ℓ y.val * (m y.val / ℓ y.val - κ P) + ℓ x.val * (κ P - m x.val / ℓ x.val)) := by
      have hx' := (hpen P hPU x.val).trans
        (mul_add_mul_eq_mul_mul_div_sub (hℓ _ hx).ne' (hβ P hPU))
      have hy' := (hpen P hPU y.val).trans
        (mul_add_mul_eq_mul_mul_div_sub (hℓ _ hy).ne' (hβ P hPU))
      rw [map_sub]
      linear_combination hy' - hx'
    have hpos : 0 < ℓ y.val * (m y.val / ℓ y.val - κ P) + ℓ x.val * (κ P - m x.val / ℓ x.val) :=
      add_pos (mul_pos (hℓ _ hy) (by linarith)) (mul_pos (hℓ _ hx) (by linarith))
    simp only [crossingLetter_def, hv, mul_pos_iff_of_pos_right hpos]
  -- Split the listed walls below the target slope at the source slope.
  have hsplit : (L.filter fun P => κ P < m y.val / ℓ y.val) =
      (L.filter fun P => κ P < m x.val / ℓ x.val) ++
        L.filter fun P => m x.val / ℓ x.val < κ P ∧ κ P < m y.val / ℓ y.val := by
    apply List.Pairwise.eq_of_mem_iff (hL.filter _)
    · refine List.pairwise_append.mpr ⟨hL.filter _, hL.filter _, fun P hP Q hQ => ?_⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hP hQ
      linarith [hP.2, hQ.2.1]
    · intro P
      simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨hPL, hPy⟩
        rcases lt_or_gt_of_ne (hxκ P hPL) with hlt | hlt
        · exact Or.inr ⟨hPL, hlt, hPy⟩
        · exact Or.inl ⟨hPL, hlt⟩
      · rintro (⟨hPL, hPx⟩ | ⟨hPL, -, hPy⟩)
        · exact ⟨hPL, hPx.trans_le hxy⟩
        · exact ⟨hPL, hPy⟩
  have hmap : ((C.orderedCrossings e).map fun a => C.crossingLetter ν x y a.1) =
      (L.filter fun P => m x.val / ℓ x.val < κ P ∧ κ P < m y.val / ℓ y.val).map fun P =>
        if 0 < β P then (FreeGroup.of P)⁻¹ else FreeGroup.of P := by
    have hcomp : (fun a : C.walls × ℝ => C.crossingLetter ν x y a.1) =
        C.crossingLetter ν x y ∘ Prod.fst := rfl
    rw [hcomp, ← List.map_map, hfst]
    exact List.map_congr_left hletter
  rw [segmentCrossingWord_def, pencilPotential, pencilPotential, hsplit, List.reverse_append,
    List.map_append, List.prod_append, mul_inv_cancel_right, List.map_reverse, List.map_reverse,
    hmap]

/-- A wall meeting the region is not parallel to the level sets of `ℓ`: its pencil
function has a nonzero `m`-coefficient. -/
private theorem coeff_ne_zero_of_pencil
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    (hℓ : ∀ z ∈ U, 0 < ℓ z)
    (hwall : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z ∈ U, z ∈ (P : Set V) ↔ ν P z = b P)
    {P : C.walls} {a c : ℝ} (hpen : ∀ z, ν P z - b P = a * ℓ z + c * m z)
    (hP : (U ∩ P).Nonempty) : c ≠ 0 := by
  have := h.finiteDimensional
  intro hc
  obtain ⟨w, hwU, hwP⟩ := hP
  have ha : a = 0 := by
    have hw := hpen w
    rw [(hwall P ⟨w, hwU, hwP⟩ w hwU).mp hwP, sub_self, hc, zero_mul, add_zero] at hw
    exact (mul_eq_zero.mp hw.symm).resolve_right (hℓ w hwU).ne'
  -- The coorientation would vanish, contradicting the codimension of the wall.
  have hzero : ν P = 0 := by
    have hb : b P = 0 := by simpa [ha, hc] using hpen 0
    ext z
    simpa [ha, hc, hb, sub_eq_zero] using hpen z
  have hdim := C.finrank_direction_add_one_of_mem_walls P.property
  rw [← hν P, hzero, LinearMap.ker_zero, finrank_top] at hdim
  omega

/-- In a convex region missing singular support, on which `ℓ` is positive, suppose
each wall meeting the region agrees there with a level set of its coorientation,
whose defining affine function lies in the pencil spanned by `ℓ` and `m`. Then
admissible polygonal paths in the region with the same endpoints have the same
crossing word. Only the vertices need to lie in the region. -/
theorem crossingWord_eq_of_pencil (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    (b : C.walls → ℝ) {U : Set V} (hU : Convex ℝ U)
    (hsing : Disjoint U (singularSupport fun P : C.walls => (P : Set V)))
    (ℓ m : V →ᵃ[ℝ] ℝ) (hℓ : ∀ z ∈ U, 0 < ℓ z)
    (hwall : ∀ P : C.walls, (U ∩ P).Nonempty → ∀ z ∈ U, z ∈ (P : Set V) ↔ ν P z = b P)
    (hpen : ∀ P : C.walls, (U ∩ P).Nonempty →
      ∃ α β : ℝ, ∀ z, ν P z - b P = α * ℓ z + β * m z)
    {x y : WallComplement (fun P : C.walls => (P : Set V))} (p q : AdmissiblePLPath x y)
    (hp : ∀ z ∈ p.vertices, z.val ∈ U) (hq : ∀ z ∈ q.vertices, z.val ∈ U) :
    p.crossingWord ν = q.crossingWord ν := by
  classical
  have := h.finiteDimensional
  choose! α β hαβ using hpen
  have hβ (P : C.walls) (hP : (U ∩ P).Nonempty) : β P ≠ 0 :=
    coeff_ne_zero_of_pencil hν hℓ hwall (hαβ P hP) hP
  set κ : C.walls → ℝ := fun P => -α P / β P with hκ
  -- Distinct walls meeting the region have distinct slopes.
  have hinj {P Q : C.walls} (hP : (U ∩ P).Nonempty) (hQ : (U ∩ Q).Nonempty)
      (hPQ : κ P = κ Q) : P = Q := by
    obtain ⟨w, hwU, hwP⟩ := hP
    have hwQ : w ∈ (Q : Set V) := (mem_iff_div_eq_of_pencil hℓ hwall hαβ hβ hQ hwU).mpr
      (((mem_iff_div_eq_of_pencil hℓ hwall hαβ hβ ⟨w, hwU, hwP⟩ hwU).mp hwP).trans hPQ)
    exact C.eq_of_mem_wall_of_notMem_singularSupport hwP hwQ
      (Set.disjoint_left.mp hsing hwU)
  -- List the walls meeting the region in increasing order of slope.
  let L := (Finset.univ.filter fun P : C.walls => (U ∩ P).Nonempty).toList.mergeSort
    fun P Q => decide (κ P ≤ κ Q)
  have hLmem (P : C.walls) : P ∈ L ↔ (U ∩ P).Nonempty := by
    simp [L, (List.mergeSort_perm _ _).mem_iff]
  have hL : L.Pairwise fun P Q => κ P < κ Q := by
    have hle := List.pairwise_mergeSort (le := fun P Q => decide (κ P ≤ κ Q))
      (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at h₁ h₂ ⊢; exact h₁.trans h₂)
      (fun P Q => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total _ _)
      (Finset.univ.filter fun P : C.walls => (U ∩ P).Nonempty).toList
    have hnd : L.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
    refine (hle.and (List.nodup_iff_pairwise_ne.mp hnd)).imp_of_mem
      fun {P Q} hP hQ hPQ => lt_of_le_of_ne (by simpa using hPQ.1) fun he => hPQ.2 ?_
    exact hinj ((hLmem P).mp hP) ((hLmem Q).mp hQ) he
  -- Every segment, hence every path, changes the potential by its word.
  have hseg {y z : WallComplement (fun P : C.walls => (P : Set V))} (e : y ⟶ z)
      (hy : y.val ∈ U) (hz : z.val ∈ U) :
      C.segmentCrossingWord ν e = pencilPotential L κ β (m z.val / ℓ z.val) *
        (pencilPotential L κ β (m y.val / ℓ y.val))⁻¹ := by
    rcases le_total (m y.val / ℓ y.val) (m z.val / ℓ z.val) with hyz | hzy
    · exact segmentCrossingWord_eq_pencilPotential_of_le hU hℓ hwall hαβ hβ hL hLmem e hy hz hyz
    · have hrev := segmentCrossingWord_eq_pencilPotential_of_le hU hℓ hwall hαβ hβ hL hLmem
        (Quiver.reverse e) hz hy hzy
      rw [C.segmentCrossingWord_reverse ν hν] at hrev
      rw [← inv_inv (C.segmentCrossingWord ν e), hrev, mul_inv_rev, inv_inv]
  have hpath {z : WallComplement (fun P : C.walls => (P : Set V))} (r : AdmissiblePLPath x z)
      (hr : ∀ w ∈ r.vertices, w.val ∈ U) :
      r.crossingWord ν = pencilPotential L κ β (m z.val / ℓ z.val) *
        (pencilPotential L κ β (m x.val / ℓ x.val))⁻¹ := by
    induction r with
    | nil => simp
    | @cons y z r e ih =>
      have hr' : ∀ w ∈ r.vertices, w.val ∈ U :=
        fun w hw => hr w ((Quiver.Path.mem_vertices_cons r e).mpr (Or.inl hw))
      rw [Quiver.Path.crossingWord_cons, ih hr',
        hseg e (hr' y r.end_mem_vertices) (hr z ((Quiver.Path.mem_vertices_cons r e).mpr
          (Or.inr rfl))), mul_assoc, inv_mul_cancel_left]
  rw [hpath p hp, hpath q hq]

end Mei.FinitePolyhedralComplex
