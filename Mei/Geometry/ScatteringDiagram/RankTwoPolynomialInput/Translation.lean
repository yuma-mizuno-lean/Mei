/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Incoming

/-!
# Generic translations of rank-two polynomial inputs

Let `I` be a rank-two polynomial input with incoming lines `{ν_j = c_j}` in `M_ℝ`. Translating
the lines by real numbers `t_j` gives the input `I.translate t` with lines `{ν_j = c_j + t_j}`
and unchanged tangents, coorientations and wall functions. We work with the cylinders over the
lines in `L_ℝ` (`RankTwoPolynomialInput.cylinder`), which are the supports of the incoming walls
(`RankTwoPolynomialInput.incomingDiagram_support_eq_cylinder`).

Two lines are transverse when their coorientations are linearly independent
(`RankTwoPolynomialInput.IsTransverse`). Since `M` has rank two, every coorientation is a rational
combination of two transverse ones, so the third coorientation is constant on the intersection
of two transverse cylinders (`RankTwoPolynomialInput.realCharacter_wallNormal_eq_of_mem_cylinder`),
and two lines that are not transverse and meet have the same cylinder
(`RankTwoPolynomialInput.cylinder_eq_of_not_isTransverse`).

A family of lines is in general position (`RankTwoPolynomialInput.IsGenericOn`) when no point lies
on three pairwise transverse lines of the family. Then at every point the lines of the family
through it have at most two distinct cylinders
(`RankTwoPolynomialInput.IsGenericOn.cylinder_eq_or_eq`). Each additional line has to avoid only
finitely many offsets, so arbitrarily small translations put any finite family in general
position (`RankTwoPolynomialInput.exists_translate_isGenericOn`). Choosing them order by order
gives one translation `t`, with `|t_j| < ε_j` for any prescribed `ε_j > 0` and `t_j = 0` on lines
without terms, for which the lines active at every order `k` are in general position
(`RankTwoPolynomialInput.exists_translate_isGenericOn_linesAtOrder`).

Such translations are the perturbations of the affine incoming lines in the setting of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, Theorem 9.9
(arXiv:2503.03719v1): after a generic translation, every point meets at most two of the active
incoming lines, up to coincident parallel lines. Comparing the completions of the translated and
the original inputs is not done here.
-/

public section

noncomputable section

open TauCeti.Toric

namespace Mei.RankTwoPolynomialInput

variable {L M ι V : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι)

section Translate

/-- Translate the incoming line `{ν_j = c_j}` to `{ν_j = c_j + t_j}`, keeping the tangents,
coorientations and wall functions. -/
def translate (t : ι → ℝ) : RankTwoPolynomialInput d M ι :=
  { I with offset := fun j => I.offset j + t j }

variable (t : ι → ℝ)

/-- Translation keeps the projection. -/
@[simp]
theorem translate_projection : (I.translate t).projection = I.projection := (rfl)

/-- Translation keeps the tangents. -/
@[simp]
theorem translate_tangent : (I.translate t).tangent = I.tangent := (rfl)

/-- Translation keeps the coorientations. -/
@[simp]
theorem translate_normal : (I.translate t).normal = I.normal := (rfl)

/-- Translation adds `t_j` to the offset of the line `j`. -/
@[simp]
theorem translate_offset (j : ι) : (I.translate t).offset j = I.offset j + t j := (rfl)

/-- Translation keeps the exponents of the wall functions. -/
@[simp]
theorem translate_exponents : (I.translate t).exponents = I.exponents := (rfl)

/-- Translation keeps the cylinder normals. -/
@[simp]
theorem wallNormal_translate : (I.translate t).wallNormal = I.wallNormal := by
  funext j
  ext q
  simp [wallNormal_apply]

/-- Translation keeps the lines active at each order. -/
@[simp]
theorem linesAtOrder_translate : (I.translate t).linesAtOrder = I.linesAtOrder := by
  funext k
  ext j
  simp

/-- The zero translation is the identity. -/
@[simp]
theorem translate_zero : I.translate 0 = I := by
  cases I
  simp [translate]

/-- Translations compose by addition. -/
theorem translate_translate (t' : ι → ℝ) :
    (I.translate t).translate t' = I.translate (t + t') := by
  simp [translate, add_assoc]

end Translate

section Cylinder

variable [AddCommGroup V] [Module ℝ V] {latticeMap : L →+ V} (h : IsIntegralLattice latticeMap)

/-- The cylinder `{x ∈ L_ℝ | ν_j(π x) = c_j}` over the incoming line `j`. -/
def cylinder (j : ι) : Set V :=
  {x | h.realCharacter (I.wallNormal j) x = I.offset j}

/-- A point lies on the cylinder over `j` when `ν_j ∘ π` takes the value `c_j` there. -/
@[simp]
theorem mem_cylinder {j : ι} {x : V} :
    x ∈ I.cylinder h j ↔ h.realCharacter (I.wallNormal j) x = I.offset j :=
  Iff.rfl

/-- The cylinder over a translated line. -/
theorem mem_cylinder_translate {t : ι → ℝ} {j : ι} {x : V} :
    x ∈ (I.translate t).cylinder h j ↔ h.realCharacter (I.wallNormal j) x = I.offset j + t j := by
  simp

/-- The cylinder over a line depends only on the offset of that line. -/
theorem cylinder_translate_eq {t t' : ι → ℝ} {j : ι} (htt' : t j = t' j) :
    (I.translate t).cylinder h j = (I.translate t').cylinder h j := by
  ext x
  simp [htt']

end Cylinder

section Diagram

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : IsIntegralLattice latticeMap) {R : Type*} [CommRing R] [DecidableEq L] [Algebra ℚ R]

/-- The incoming walls over a line are supported on its cylinder. -/
theorem incomingDiagram_support_eq_cylinder (I : RankTwoPolynomialInput d M ι)
    (c : I.Variable → R) (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).support = I.cylinder h j.1 := by
  ext x
  simp

end Diagram

/-- Two incoming lines are transverse when their coorientations are linearly independent. -/
def IsTransverse (a b : ι) : Prop :=
  LinearIndependent ℤ ![I.normal a, I.normal b]

variable {I}

/-- Two lines are transverse exactly when their coorientations are linearly independent. -/
theorem isTransverse_iff {a b : ι} :
    I.IsTransverse a b ↔ LinearIndependent ℤ ![I.normal a, I.normal b] :=
  Iff.rfl

/-- Transversality is symmetric. -/
theorem IsTransverse.symm {a b : ι} (hab : I.IsTransverse a b) : I.IsTransverse b a :=
  LinearIndependent.pair_symm_iff.mp hab

/-- A line is not transverse to itself. -/
theorem IsTransverse.ne {a b : ι} (hab : I.IsTransverse a b) : a ≠ b := by
  rintro rfl
  exact absurd (hab.injective (a₁ := 0) (a₂ := 1) rfl) (by decide)

/-- Translation keeps transversality. -/
@[simp]
theorem isTransverse_translate {t : ι → ℝ} {a b : ι} :
    (I.translate t).IsTransverse a b ↔ I.IsTransverse a b := by
  simp [IsTransverse]

section Relation

variable [AddCommGroup V] [Module ℝ V] {latticeMap : L →+ V} {h : IsIntegralLattice latticeMap}

/-- An integral relation between coorientations gives the same relation between the real
cylinder normals. -/
theorem realCharacter_wallNormal_of_smul_normal_eq {a b c : ι} {p q r : ℤ}
    (hpqr : r • I.normal c = p • I.normal a + q • I.normal b)
    (x : V) :
    (r : ℝ) * h.realCharacter (I.wallNormal c) x =
      p * h.realCharacter (I.wallNormal a) x + q * h.realCharacter (I.wallNormal b) x := by
  have hw : r • I.wallNormal c = p • I.wallNormal a + q • I.wallNormal b := by
    ext n
    simpa [wallNormal_apply] using LinearMap.congr_fun hpqr (I.projection n)
  simpa [map_zsmul, ← zsmul_eq_mul] using LinearMap.congr_fun (congrArg h.realCharacter hw) x

/-- Two lines that are not transverse and meet have the same cylinder. -/
theorem cylinder_eq_of_not_isTransverse {a b : ι} (hab : ¬ I.IsTransverse a b)
    (hx : (I.cylinder h a ∩ I.cylinder h b).Nonempty) : I.cylinder h a = I.cylinder h b := by
  obtain ⟨x, hxa, hxb⟩ := hx
  obtain ⟨p, q, hpq, hne⟩ : ∃ p q : ℤ, p • I.normal a + q • I.normal b = 0 ∧ (p = 0 → q ≠ 0) := by
    simpa [IsTransverse, LinearIndependent.pair_iff, not_and_or] using hab
  have hp : p ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add, smul_eq_zero] at hpq
    exact (I.isPrimitive_normal b).ne_zero (hpq.resolve_left (hne rfl))
  have hq : q ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero, smul_eq_zero] at hpq
    exact (I.isPrimitive_normal a).ne_zero (hpq.resolve_left hp)
  have hrel : (-q) • I.normal b = p • I.normal a + 0 • I.normal b := by
    rw [zero_smul, add_zero, neg_smul, neg_eq_iff_add_eq_zero, add_comm]
    exact hpq
  have key : ∀ y : V, (-q : ℝ) * h.realCharacter (I.wallNormal b) y =
      p * h.realCharacter (I.wallNormal a) y := fun y => by
    simpa using realCharacter_wallNormal_of_smul_normal_eq (h := h) hrel y
  have hpR : (p : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hp
  have hqR : (-q : ℝ) ≠ 0 := neg_ne_zero.mpr (Int.cast_ne_zero.mpr hq)
  ext y
  rw [mem_cylinder, mem_cylinder, ← (I.mem_cylinder h).mp hxa, ← (I.mem_cylinder h).mp hxb]
  constructor
  · intro hy
    apply mul_left_cancel₀ hqR
    rw [key, key, hy]
  · intro hy
    apply mul_left_cancel₀ hpR
    rw [← key, ← key, hy]

end Relation

section Rank

variable [Module.Free ℤ M] [Module.Finite ℤ M]

/-- In rank two, a nonzero multiple of every coorientation is an integral combination of two
transverse coorientations. -/
theorem IsTransverse.exists_smul_normal_eq {a b : ι} (hab : I.IsTransverse a b) (c : ι) :
    ∃ p q r : ℤ, r ≠ 0 ∧ r • I.normal c = p • I.normal a + q • I.normal b := by
  have hrank : Module.finrank ℤ (Module.Dual ℤ M) = 2 := by
    rw [← I.finrank_eq_two, Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ M).dualBasis,
      Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ M)]
  have hdep : ¬ LinearIndependent ℤ ![I.normal a, I.normal b, I.normal c] := fun hli => by
    simpa [hrank] using hli.fintype_card_le_finrank
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hg
  have hg2 : g 2 ≠ 0 := by
    intro h2
    rw [h2, zero_smul, add_zero] at hg
    obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hab (g 0) (g 1) hg
    fin_cases i <;> simp_all
  refine ⟨-g 0, -g 1, g 2, hg2, ?_⟩
  rw [neg_smul, neg_smul, ← neg_add, eq_neg_iff_add_eq_zero, add_comm]
  exact hg

variable [AddCommGroup V] [Module ℝ V] {latticeMap : L →+ V} {h : IsIntegralLattice latticeMap}

/-- The cylinder normal of every line is constant on the intersection of the cylinders over two
transverse lines. -/
theorem realCharacter_wallNormal_eq_of_mem_cylinder {a b : ι} (hab : I.IsTransverse a b)
    (c : ι) {x y : V} (hx : x ∈ I.cylinder h a ∩ I.cylinder h b)
    (hy : y ∈ I.cylinder h a ∩ I.cylinder h b) :
    h.realCharacter (I.wallNormal c) x = h.realCharacter (I.wallNormal c) y := by
  obtain ⟨p, q, r, hr, hpqr⟩ := hab.exists_smul_normal_eq c
  have hxy := realCharacter_wallNormal_of_smul_normal_eq (h := h) hpqr x
  rw [(I.mem_cylinder h).mp hx.1, (I.mem_cylinder h).mp hx.2, ← (I.mem_cylinder h).mp hy.1,
    ← (I.mem_cylinder h).mp hy.2, ← realCharacter_wallNormal_of_smul_normal_eq hpqr y] at hxy
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hr) hxy

end Rank

section Generic

variable [AddCommGroup V] [Module ℝ V] {latticeMap : L →+ V} (h : IsIntegralLattice latticeMap)

variable (I) in
/-- The lines indexed by `s` are in general position: no point lies on the cylinders over three
pairwise transverse lines of `s`. -/
def IsGenericOn (s : Set ι) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, I.IsTransverse a b → I.IsTransverse a c → I.IsTransverse b c →
    I.cylinder h a ∩ I.cylinder h b ∩ I.cylinder h c = ∅

variable {h}

/-- A family is in general position exactly when no point lies on three pairwise transverse lines
of the family. -/
theorem isGenericOn_iff {s : Set ι} :
    I.IsGenericOn h s ↔ ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, I.IsTransverse a b → I.IsTransverse a c →
      I.IsTransverse b c → I.cylinder h a ∩ I.cylinder h b ∩ I.cylinder h c = ∅ :=
  Iff.rfl

/-- In a family in general position, the cylinders over three pairwise transverse lines have no
common point. -/
theorem IsGenericOn.inter_eq_empty {s : Set ι} (hs : I.IsGenericOn h s) {a b c : ι} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : I.IsTransverse a b) (hac : I.IsTransverse a c)
    (hbc : I.IsTransverse b c) : I.cylinder h a ∩ I.cylinder h b ∩ I.cylinder h c = ∅ :=
  hs a ha b hb c hc hab hac hbc

/-- A subfamily of a family in general position is in general position. -/
theorem IsGenericOn.mono {s s' : Set ι} (hs : I.IsGenericOn h s) (hss' : s' ⊆ s) :
    I.IsGenericOn h s' := fun a ha b hb c hc =>
  hs a (hss' ha) b (hss' hb) c (hss' hc)

/-- The empty family is in general position. -/
theorem isGenericOn_empty : I.IsGenericOn h ∅ := fun _ ha => ha.elim

/-- General position of the translated lines of `s` depends only on the translations of the
lines of `s`. -/
theorem isGenericOn_translate_congr {s : Set ι} {t t' : ι → ℝ} (htt' : ∀ j ∈ s, t j = t' j) :
    (I.translate t).IsGenericOn h s ↔ (I.translate t').IsGenericOn h s := by
  simp only [IsGenericOn, isTransverse_translate]
  refine forall₂_congr fun a ha => forall₂_congr fun b hb => forall₂_congr fun c hc => ?_
  rw [I.cylinder_translate_eq h (htt' a ha), I.cylinder_translate_eq h (htt' b hb),
    I.cylinder_translate_eq h (htt' c hc)]

/-- Adding a line to a family in general position keeps general position when the new line meets
no intersection of two transverse lines of the family that are both transverse to it. -/
theorem IsGenericOn.insert {s : Set ι} {j : ι} (hs : I.IsGenericOn h s)
    (hj : ∀ a ∈ s, ∀ b ∈ s, I.IsTransverse a b → I.IsTransverse a j → I.IsTransverse b j →
      I.cylinder h a ∩ I.cylinder h b ∩ I.cylinder h j = ∅) :
    I.IsGenericOn h (insert j s) := by
  rintro a (rfl | ha) b (rfl | hb) c (rfl | hc) hab hac hbc
  · exact (hab.ne rfl).elim
  · exact (hab.ne rfl).elim
  · exact (hac.ne rfl).elim
  · rw [Set.inter_assoc, Set.inter_comm]
    exact hj b hb c hc hbc hab.symm hac.symm
  · exact (hbc.ne rfl).elim
  · rw [Set.inter_right_comm]
    exact hj a ha c hc hac hab hbc.symm
  · exact hj a ha b hb hab hac hbc
  · exact hs a ha b hb c hc hab hac hbc

/-- In a family in general position, the lines through a point on two transverse lines of the
family have the cylinder of one of these two lines. -/
theorem IsGenericOn.cylinder_eq_or_eq {s : Set ι} (hs : I.IsGenericOn h s) {a b c : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : I.IsTransverse a b) {x : V}
    (hx : x ∈ I.cylinder h a ∩ I.cylinder h b ∩ I.cylinder h c) :
    I.cylinder h c = I.cylinder h a ∨ I.cylinder h c = I.cylinder h b := by
  by_cases hac : I.IsTransverse a c
  · by_cases hbc : I.IsTransverse b c
    · exact ((hs a ha b hb c hc hab hac hbc).subset hx).elim
    · exact Or.inr (cylinder_eq_of_not_isTransverse hbc ⟨x, hx.1.2, hx.2⟩).symm
  · exact Or.inl (cylinder_eq_of_not_isTransverse hac ⟨x, hx.1.1, hx.2⟩).symm

variable [Module.Free ℤ M] [Module.Finite ℤ M]

/-- If the lines of a finite set `s` translated by `t` are in general position and `j ∉ s`, then
changing the translation of the line `j` to some `x` with `|x| < ε` puts the lines of
`insert j s` in general position. -/
theorem exists_isGenericOn_translate_update [DecidableEq ι] {s : Set ι} (hs : s.Finite) {t : ι → ℝ}
    (ht : (I.translate t).IsGenericOn h s) {j : ι} (hj : j ∉ s) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, |x| < ε ∧ (I.translate (Function.update t j x)).IsGenericOn h (insert j s) := by
  let bad : Set ℝ := ⋃ p ∈ s ×ˢ s, {v | I.IsTransverse p.1 p.2 ∧
    ∃ y ∈ (I.translate t).cylinder h p.1 ∩ (I.translate t).cylinder h p.2,
      v = h.realCharacter (I.wallNormal j) y - I.offset j}
  have hbad : bad.Finite := (hs.prod hs).biUnion fun p _ => Set.Subsingleton.finite <| by
    rintro _ ⟨hp, y, hy, rfl⟩ _ ⟨-, z, hz, rfl⟩
    have := realCharacter_wallNormal_eq_of_mem_cylinder (I := I.translate t)
      (isTransverse_translate.mpr hp) j hy hz
    rw [wallNormal_translate] at this
    rw [this]
  obtain ⟨x, hx, hxbad⟩ := ((Set.Ioo_infinite (neg_lt_self hε)).sdiff hbad).nonempty
  refine ⟨x, abs_lt.mpr hx, ?_⟩
  have hsame : ∀ i ∈ s, Function.update t j x i = t i := fun i hi =>
    Function.update_of_ne (by rintro rfl; exact hj hi) _ _
  refine ((isGenericOn_translate_congr hsame).mpr ht).insert fun a ha b hb hab _ _ => ?_
  refine Set.eq_empty_of_forall_notMem fun y hy => hxbad ?_
  refine Set.mem_biUnion (x := (a, b)) (Set.mk_mem_prod ha hb)
    ⟨isTransverse_translate.mp hab, y, ?_, ?_⟩
  · exact ⟨(I.cylinder_translate_eq h (hsame a ha)).subset hy.1.1,
      (I.cylinder_translate_eq h (hsame b hb)).subset hy.1.2⟩
  · have := (I.mem_cylinder_translate h).mp hy.2
    rw [Function.update_self] at this
    linarith

/-- If the lines of a finite set `s` translated by `t` are in general position and `|t_j| < ε_j`
for all `j`, then changing `t` only on a finite set `u`, keeping `|t_j| < ε_j`, puts the lines of
`s ∪ u` in general position. -/
theorem exists_translate_isGenericOn {s u : Set ι} (hs : s.Finite) (hu : u.Finite)
    {t : ι → ℝ} (ht : (I.translate t).IsGenericOn h s) {ε : ι → ℝ} (htε : ∀ j, |t j| < ε j) :
    ∃ t' : ι → ℝ, (∀ j, |t' j| < ε j) ∧ (∀ j ∉ u, t' j = t j) ∧
      (I.translate t').IsGenericOn h (s ∪ u) := by
  classical
  induction u, hu using Set.Finite.induction_on with
  | empty => exact ⟨t, htε, fun _ _ => rfl, by rwa [Set.union_empty]⟩
  | @insert j u hju hu ih =>
    obtain ⟨t', ht'ε, ht't, ht'⟩ := ih
    by_cases hjs : j ∈ s
    · refine ⟨t', ht'ε, fun i hi => ht't i fun hiu => hi (Set.mem_insert_of_mem _ hiu), ?_⟩
      rwa [Set.union_insert, Set.insert_eq_of_mem (Set.mem_union_left _ hjs)]
    have hεj : 0 < ε j := (abs_nonneg _).trans_lt (htε j)
    obtain ⟨x, hx, hgen⟩ := exists_isGenericOn_translate_update (hs.union hu) ht'
      (fun h' => h'.elim hjs hju) hεj
    refine ⟨Function.update t' j x, fun i => ?_, fun i hi => ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | hij
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hij]
        exact ht'ε i
    · rw [Function.update_of_ne (by rintro rfl; exact hi (Set.mem_insert _ _))]
      exact ht't i fun hiu => hi (Set.mem_insert_of_mem _ hiu)
    · rwa [Set.union_insert]

/-- One step of the order-by-order choice: general position of the lines active at order `k`
extends to order `k + 1` by translating only the newly active lines. -/
theorem exists_translate_isGenericOn_linesAtOrder_succ {k : ℕ} {t : ι → ℝ}
    (ht : (I.translate t).IsGenericOn h (I.linesAtOrder k)) {ε : ι → ℝ}
    (htε : ∀ j, |t j| < ε j) :
    ∃ t' : ι → ℝ, (∀ j, |t' j| < ε j) ∧ (∀ j ∉ I.linesAtOrder (k + 1) \ I.linesAtOrder k,
      t' j = t j) ∧ (I.translate t').IsGenericOn h (I.linesAtOrder (k + 1)) := by
  obtain ⟨t', h₁, h₂, h₃⟩ := exists_translate_isGenericOn (I.finite_linesAtOrder k)
    ((I.finite_linesAtOrder (k + 1)).sdiff) ht htε
  refine ⟨t', h₁, h₂, ?_⟩
  rwa [Set.union_sdiff_cancel (I.linesAtOrder_mono k.le_succ)] at h₃

variable (I h) in
/-- Generic translations chosen order by order: a sequence `t_k` of translations with
`|t_k j| < ε_j`, vanishing off the lines active at order `k`, putting the lines active at order
`k` in general position, and with `t_{k+1}` agreeing with `t_k` on the lines active at order
`k`. -/
theorem exists_seq_translate_isGenericOn_linesAtOrder {ε : ι → ℝ} (hε : ∀ j, 0 < ε j) :
    ∃ t : ℕ → ι → ℝ, (∀ k j, |t k j| < ε j) ∧ (∀ k, ∀ j ∉ I.linesAtOrder k, t k j = 0) ∧
      (∀ k, (I.translate (t k)).IsGenericOn h (I.linesAtOrder k)) ∧
      ∀ k, ∀ j ∈ I.linesAtOrder k, t (k + 1) j = t k j := by
  let P : ℕ → (ι → ℝ) → Prop := fun k t => (∀ j, |t j| < ε j) ∧
    (∀ j ∉ I.linesAtOrder k, t j = 0) ∧ (I.translate t).IsGenericOn h (I.linesAtOrder k)
  have base : ∃ t, P 0 t := by
    obtain ⟨t, h₁, h₂, h₃⟩ := exists_translate_isGenericOn Set.finite_empty
      (I.finite_linesAtOrder 0) (t := 0) (isGenericOn_empty : (I.translate 0).IsGenericOn h ∅)
      fun j => by simpa using hε j
    exact ⟨t, h₁, h₂, by rwa [Set.empty_union] at h₃⟩
  have step : ∀ k t, P k t → ∃ t', P (k + 1) t' ∧ ∀ j ∈ I.linesAtOrder k, t' j = t j := by
    rintro k t ⟨h₁, h₂, h₃⟩
    obtain ⟨t', h₁', h₂', h₃'⟩ := exists_translate_isGenericOn_linesAtOrder_succ h₃ h₁
    refine ⟨t', ⟨h₁', fun j hj => ?_, h₃'⟩, fun j hj => h₂' j fun hj' => hj'.2 hj⟩
    rw [h₂' j fun hj' => hj hj'.1]
    exact h₂ j fun hjk => hj (I.linesAtOrder_mono k.le_succ hjk)
  let seq : (k : ℕ) → {t // P k t} := fun k => Nat.rec ⟨base.choose, base.choose_spec⟩
    (fun k t => ⟨(step k t.1 t.2).choose, (step k t.1 t.2).choose_spec.1⟩) k
  exact ⟨fun k => (seq k).1, fun k => (seq k).2.1, fun k => (seq k).2.2.1,
    fun k => (seq k).2.2.2, fun k => (step k (seq k).1 (seq k).2).choose_spec.2⟩

variable (I h) in
/-- **Generic translations.** For any bounds `ε_j > 0` there is a translation `t` with
`|t_j| < ε_j`, vanishing on the lines without terms, such that at every order `k` the translated
lines with a term of degree at most `k` are in general position. -/
theorem exists_translate_isGenericOn_linesAtOrder {ε : ι → ℝ} (hε : ∀ j, 0 < ε j) :
    ∃ t : ι → ℝ, (∀ j, |t j| < ε j) ∧ (∀ j, (∀ k, j ∉ I.linesAtOrder k) → t j = 0) ∧
      ∀ k, (I.translate t).IsGenericOn h (I.linesAtOrder k) := by
  classical
  obtain ⟨seq, hsmall, -, hgen, hsucc⟩ := I.exists_seq_translate_isGenericOn_linesAtOrder h hε
  have hseq : ∀ k j, j ∈ I.linesAtOrder k → ∀ m, k ≤ m → seq m j = seq k j := by
    intro k j hj m hkm
    induction m, hkm using Nat.le_induction with
    | base => rfl
    | succ m hkm ih => rw [hsucc m j (I.linesAtOrder_mono hkm hj), ih]
  let t : ι → ℝ := fun j => if hj : ∃ k, j ∈ I.linesAtOrder k then seq (Nat.find hj) j else 0
  have ht : ∀ k, ∀ j ∈ I.linesAtOrder k, t j = seq k j := fun k j hj => by
    have hex : ∃ k, j ∈ I.linesAtOrder k := ⟨k, hj⟩
    simp only [t, hex, ↓reduceDIte]
    exact (hseq _ j (Nat.find_spec hex) k (Nat.find_min' hex hj)).symm
  refine ⟨t, fun j => ?_, fun j hj => dite_eq_right_iff.mpr fun hex =>
    (hj _ hex.choose_spec).elim, fun k => (isGenericOn_translate_congr (ht k)).mpr (hgen k)⟩
  by_cases hex : ∃ k, j ∈ I.linesAtOrder k
  · simp only [t, hex, ↓reduceDIte]
    exact hsmall _ j
  · simp only [t, hex, ↓reduceDIte]
    simpa using hε j

end Generic

end Mei.RankTwoPolynomialInput
