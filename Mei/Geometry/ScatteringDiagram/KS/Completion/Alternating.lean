/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Completion
public import Mei.Geometry.ScatteringDiagram.HyperplanePair

/-!
# Completed diagrams whose complexes alternate

Fix nonzero allowed degrees `a` and `b` and a completed BCH group element `x` whose every
cutoff projection lies in the group of the Lie algebra orthogonal to the hyperplane
`ker (evaluation at b)` of the continuous dual.
Cut the dual space by that hyperplane at even cutoffs, and by it and
the hyperplane `ker (evaluation at a)` at odd cutoffs. The projection of `x` labels the
walls inside the first hyperplane and `1` labels the rest. This is a `CompletedDiagram`
(`CompletedDiagram.alternating`): the diagrams at successive cutoffs agree on common
admissible paths because the diagram on two hyperplanes is a compatible refinement of the one
on a single hyperplane with the same labels. When some continuous linear functional `θ`
satisfies `θ (j b) = 0` and `θ (j a) ≠ 0`, the complexes do not stabilize
(`CompletedDiagram.not_eventually_alternatingComplex_eq`), so a completed diagram need not be
presented by a single complex. For `N = ℤ²` and the positive monoid `ℕ²` this gives
`CompletedDiagram.exists_completedDiagram_not_eventually_eq_orthant`.

The compatible-sequence definition of completed diagrams follows Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416), Definition 2.3. The comparison of the two
cutoff diagrams is `FiniteWallDiagram.IsCompatibleRefinement.pathProduct_eq`.
-/

public section

noncomputable section

open Set Mei.Convex Mei.FinitePolyhedralComplex

namespace Mei.CompletedDiagram

section Stage

variable {N W : Type*} [AddCommGroup N] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {j : N →+ W} (h : TauCeti.Toric.IsIntegralLattice j) (a b : N)

/-- The complex of a stage: the hyperplane `ker (evaluation at b)` for `true`, and that
hyperplane together with `ker (evaluation at a)` for `false`, in the continuous dual. -/
abbrev stageComplex : Bool → FinitePolyhedralComplex h.continuousDual
  | true => hyperplaneComplex (ContinuousLinearMap.apply ℝ ℝ (j b))
      (h.isRationalFunctional_continuousDual_eval b)
  | false => hyperplanePairComplex (ContinuousLinearMap.apply ℝ ℝ (j b))
      (ContinuousLinearMap.apply ℝ ℝ (j a)) (h.isRationalFunctional_continuousDual_eval b)
      (h.isRationalFunctional_continuousDual_eval a)

/-- The complex of the cutoff `k`: the one-hyperplane complex at even cutoffs and the
two-hyperplane complex at odd ones. -/
abbrev alternatingComplex (k : ℕ) : FinitePolyhedralComplex h.continuousDual :=
  stageComplex h a b (decide (Even k))

variable {h a b}

/-- Every wall of the one-hyperplane stage is the hyperplane `ker (evaluation at b)`. -/
theorem eq_ker_of_mem_stageComplex_true_walls {P : Set (W →L[ℝ] ℝ)}
    (hP : P ∈ (stageComplex h a b true).walls) : P = {θ | θ (j b) = 0} :=
  eq_ker_of_mem_hyperplaneComplex_walls _ hP

/-- Every wall of the two-hyperplane stage lies in one of the two kernels. -/
theorem subset_ker_of_mem_stageComplex_false_walls {P : Set (W →L[ℝ] ℝ)}
    (hP : P ∈ (stageComplex h a b false).walls) :
    P ⊆ {θ | θ (j b) = 0} ∨ P ⊆ {θ | θ (j a) = 0} :=
  exists_subset_ker_of_mem_hyperplanePairComplex_walls _ _ hP

/-- The complexes of the alternating completed diagram never stabilize when some continuous
linear functional `θ` satisfies `θ (j b) = 0` and `θ (j a) ≠ 0`: the hyperplane
`ker (evaluation at b)` is a cell of the even complexes but not of the odd ones. -/
theorem not_eventually_alternatingComplex_eq
    (hb : ContinuousLinearMap.apply ℝ ℝ (j b) ≠ 0)
    (hab : ∃ θ : W →L[ℝ] ℝ, θ (j b) = 0 ∧ θ (j a) ≠ 0) :
    ¬∃ n, ∀ k ≥ n, alternatingComplex h a b k = alternatingComplex h a b (k + 1) := by
  rintro ⟨n, hn⟩
  obtain ⟨θ₀, hθb, hθa⟩ := hab
  have h2n := hn (2 * n) (by omega)
  have hev : decide (Even (2 * n)) = true := by simp
  have hod : decide (Even (2 * n + 1)) = false := by simp
  unfold alternatingComplex at h2n
  rw [hev, hod] at h2n
  exact hyperplaneComplex_ne_hyperplanePairComplex _ _ hb (θ₀ := θ₀) hθb hθa h2n

end Stage

section Diagram

variable {N W R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {j : N →+ W} (h : TauCeti.Toric.IsIntegralLattice j)
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {a b : N}

variable (j) in
/-- The labels admitted on the hyperplane `ker (evaluation at b)` at cutoff `k`: the
exponential of the Lie algebra orthogonal to that hyperplane. -/
def hyperplaneLabels (b : N) (k : ℕ) : Subgroup (d.truncatedGroup ℒ k) :=
  (orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
    ((KSSpace.continuousDual h).evaluation '' {θ : W →L[ℝ] ℝ | θ (j b) = 0})).bchSubgroup

variable {h d ℒ}

theorem hyperplaneLabels_def (b : N) (k : ℕ) :
    hyperplaneLabels j h d ℒ b k =
      (orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
        ((KSSpace.continuousDual h).evaluation '' {θ : W →L[ℝ] ℝ | θ (j b) = 0})).bchSubgroup :=
  (rfl)

/-- A group element is an admissible label on the hyperplane `ker (evaluation at b)` exactly
when its logarithm lies in the orthogonal Lie subalgebra. -/
@[simp]
theorem mem_hyperplaneLabels {b : N} {k : ℕ} (g : d.truncatedGroup ℒ k) :
    g ∈ hyperplaneLabels j h d ℒ b k ↔
      BCHGroup.log g ∈ orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
        ((KSSpace.continuousDual h).evaluation '' {θ : W →L[ℝ] ℝ | θ (j b) = 0}) :=
  LieSubalgebra.mem_bchSubgroup _ _

open scoped Classical in
/-- The KS complex of a stage at cutoff `k`. At `true`, the unique wall `ker (evaluation at b)`
carries `g` and is cooriented by `b`. At `false`, the walls inside that hyperplane carry `g`
and are cooriented by `b`, and the other walls, which lie in `ker (evaluation at a)`, carry
`1` and are cooriented by `a`. -/
def stageKS (hb : b ∈ d.monoid) (hb0 : b ≠ 0) (ha : a ∈ d.monoid) (ha0 : a ≠ 0) {k : ℕ}
    (g : d.truncatedGroup ℒ k) (hg : g ∈ hyperplaneLabels j h d ℒ b k) :
    ∀ t : Bool, KSComplex (KSSpace.continuousDual h) d ℒ (stageComplex h a b t) k
  | true =>
    { isConical := isConical_hyperplaneComplex _
      degree _ := b
      degree_mem _ := hb
      degree_ne_zero _ := hb0
      evaluation_eq_zero P θ hθ := by
        simpa [eq_ker_of_mem_stageComplex_true_walls P.property] using hθ
      label _ := g
      label_mem P := by
        rw [eq_ker_of_mem_stageComplex_true_walls P.property]
        exact hg }
  | false =>
    { isConical := isConical_hyperplanePairComplex _ _
      degree Q := if (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0} then b else a
      degree_mem _ := by split_ifs <;> assumption
      degree_ne_zero _ := by split_ifs <;> assumption
      evaluation_eq_zero Q θ hθ := by
        by_cases hQ : (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}
        · simpa [hQ] using hQ hθ
        · have hQa := (subset_ker_of_mem_stageComplex_false_walls Q.property).resolve_left hQ
          simpa [hQ] using hQa hθ
      label Q := if (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0} then g else 1
      label_mem Q := by
        by_cases hQ : (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}
        · simp only [hQ, ↓reduceIte]
          exact (LieSubalgebra.bchSubgroup_le_bchSubgroup.mpr
            (orthogonalLieSubalgebra_antitone _ (Set.image_mono hQ))) hg
        · simp only [hQ, ↓reduceIte]
          exact one_mem _ }

variable (hb : b ∈ d.monoid) (hb0 : b ≠ 0) (ha : a ∈ d.monoid) (ha0 : a ≠ 0) {k : ℕ}
  (g : d.truncatedGroup ℒ k) (hg : g ∈ hyperplaneLabels j h d ℒ b k)

/-- At the one-hyperplane stage the wall carries `g`. -/
@[simp]
theorem stageKS_true_label (P : (stageComplex h a b true).walls) :
    (stageKS hb hb0 ha ha0 g hg true).label P = g := (rfl)

/-- At the one-hyperplane stage the wall is cooriented by `b`. -/
@[simp]
theorem stageKS_true_degree (P : (stageComplex h a b true).walls) :
    (stageKS hb hb0 ha ha0 g hg true).degree P = b := (rfl)

/-- At the two-hyperplane stage, a wall inside `ker (evaluation at b)` carries `g`. -/
@[simp]
theorem stageKS_false_label_of_subset {Q : (stageComplex h a b false).walls}
    (hQ : (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}) :
    (stageKS hb hb0 ha ha0 g hg false).label Q = g := by
  classical
  simp [stageKS, hQ]

/-- At the two-hyperplane stage, a wall not inside `ker (evaluation at b)` carries `1`. -/
@[simp]
theorem stageKS_false_label_of_not_subset
    {Q : (stageComplex h a b false).walls}
    (hQ : ¬(Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}) :
    (stageKS hb hb0 ha ha0 g hg false).label Q = 1 := by
  classical
  simp [stageKS, hQ]

/-- At the two-hyperplane stage, a wall inside `ker (evaluation at b)` is cooriented by `b`. -/
@[simp]
theorem stageKS_false_degree_of_subset {Q : (stageComplex h a b false).walls}
    (hQ : (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}) :
    (stageKS hb hb0 ha ha0 g hg false).degree Q = b := by
  classical
  simp [stageKS, hQ]

/-- At the two-hyperplane stage, a wall not inside `ker (evaluation at b)` is cooriented
by `a`. -/
@[simp]
theorem stageKS_false_degree_of_not_subset
    {Q : (stageComplex h a b false).walls}
    (hQ : ¬(Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}) :
    (stageKS hb hb0 ha ha0 g hg false).degree Q = a := by
  classical
  simp [stageKS, hQ]

/-- The one-hyperplane stage forgets to the diagram with a single wall. -/
@[simp]
theorem toFiniteWallDiagram_stageKS_true :
    (stageKS hb hb0 ha ha0 g hg true).toFiniteWallDiagram =
      FiniteWallDiagram.hyperplaneDiagram (h.isRationalFunctional_continuousDual_eval b)
        (h.apply_ne_zero hb0) g := by
  refine FiniteWallDiagram.ext (funext fun P => ?_) (funext fun P => ?_)
  · ext θ
    simp [stageKS]
  · simp [stageKS]

/-- The two-hyperplane stage forgets to the diagram with labels `g` and `1`. -/
@[simp]
theorem toFiniteWallDiagram_stageKS_false :
    (stageKS hb hb0 ha ha0 g hg false).toFiniteWallDiagram =
      FiniteWallDiagram.hyperplanePairDiagram (h.isRationalFunctional_continuousDual_eval b)
        (h.isRationalFunctional_continuousDual_eval a)
        (h.apply_ne_zero hb0)
        (h.apply_ne_zero ha0) g := by
  refine FiniteWallDiagram.ext (funext fun Q => ?_) (funext fun Q => ?_)
  · by_cases hQ : (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}
    · rw [FiniteWallDiagram.hyperplanePairDiagram_normal_of_subset _ _ _ _ _ hQ]
      ext θ
      simp [stageKS, hQ]
    · rw [FiniteWallDiagram.hyperplanePairDiagram_normal_of_not_subset _ _ _ _ _ hQ]
      ext θ
      simp [stageKS, hQ]
  · by_cases hQ : (Q : Set (W →L[ℝ] ℝ)) ⊆ {θ | θ (j b) = 0}
    · rw [FiniteWallDiagram.hyperplanePairDiagram_label_of_subset _ _ _ _ _ hQ]
      simp [stageKS, hQ]
    · rw [FiniteWallDiagram.hyperplanePairDiagram_label_of_not_subset _ _ _ _ _ hQ]
      simp [stageKS, hQ]

variable {g} {g' : d.truncatedGroup ℒ (k + 1)} (hg' : g' ∈ hyperplaneLabels j h d ℒ b (k + 1))
  (hπ : (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap g' = g)

include hπ in
/-- Projecting the two-hyperplane diagram of `g'` agrees with the one-hyperplane diagram of
its projection `g` on paths with the same vertices. -/
theorem truncationMap_pathProduct_stageKS_false
    {x y : WallComplement (fun P : (stageComplex h a b true).walls => (P : Set (W →L[ℝ] ℝ)))}
    {x' y' : WallComplement (fun P : (stageComplex h a b false).walls => (P : Set (W →L[ℝ] ℝ)))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
      ((stageKS hb hb0 ha ha0 g' hg' false).toFiniteWallDiagram.pathProduct q) =
      (stageKS hb hb0 ha ha0 g hg true).toFiniteWallDiagram.pathProduct p := by
  rw [← FiniteWallDiagram.pathProduct_relabel, toFiniteWallDiagram_stageKS_false,
    FiniteWallDiagram.relabel_hyperplanePairDiagram, hπ, toFiniteWallDiagram_stageKS_true]
  exact (FiniteWallDiagram.isCompatibleRefinement_hyperplanePairDiagram _ _ _ _ _).pathProduct_eq
    q p hpq.symm

include hπ in
/-- Projecting the one-hyperplane diagram of `g'` agrees with the two-hyperplane diagram of
its projection `g` on paths with the same vertices. -/
theorem truncationMap_pathProduct_stageKS_true
    {x y : WallComplement (fun P : (stageComplex h a b false).walls => (P : Set (W →L[ℝ] ℝ)))}
    {x' y' : WallComplement (fun P : (stageComplex h a b true).walls => (P : Set (W →L[ℝ] ℝ)))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
      ((stageKS hb hb0 ha ha0 g' hg' true).toFiniteWallDiagram.pathProduct q) =
      (stageKS hb hb0 ha ha0 g hg false).toFiniteWallDiagram.pathProduct p := by
  rw [← FiniteWallDiagram.pathProduct_relabel, toFiniteWallDiagram_stageKS_true,
    FiniteWallDiagram.relabel_hyperplaneDiagram, hπ, toFiniteWallDiagram_stageKS_false]
  exact ((FiniteWallDiagram.isCompatibleRefinement_hyperplanePairDiagram
    (H := d.truncatedGroup ℒ k) _ _ _ _ _).pathProduct_eq p q hpq).symm

include hπ in
/-- The projection of the diagram of a stage at one cutoff agrees with the diagram of the next
stage at the previous cutoff on paths with the same vertices. -/
theorem truncationMap_pathProduct_stageKS (t t' : Bool) (ht : t' = !t)
    {x y : WallComplement (fun P : (stageComplex h a b t).walls => (P : Set (W →L[ℝ] ℝ)))}
    {x' y' : WallComplement (fun P : (stageComplex h a b t').walls => (P : Set (W →L[ℝ] ℝ)))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
      ((stageKS hb hb0 ha ha0 g' hg' t').toFiniteWallDiagram.pathProduct q) =
      (stageKS hb hb0 ha ha0 g hg t).toFiniteWallDiagram.pathProduct p := by
  subst ht
  cases t
  · exact truncationMap_pathProduct_stageKS_true hb hb0 ha ha0 hg hg' hπ p q hpq
  · exact truncationMap_pathProduct_stageKS_false hb hb0 ha ha0 hg hg' hπ p q hpq

/-- The completed diagram whose complexes alternate between one and two hyperplanes, and whose
walls inside `ker (evaluation at b)` carry the projections of the completed group element
`x`, all other walls carrying `1`. -/
def alternating (x : d.completedBCHGroup ℒ)
    (hx : ∀ k, CompletedGroup.projection k x ∈ hyperplaneLabels j h d ℒ b k) :
    CompletedDiagram (KSSpace.continuousDual h) d ℒ (alternatingComplex h a b) where
  diagram k := stageKS hb hb0 ha ha0 (CompletedGroup.projection k x) (hx k) (decide (Even k))
  compatible k _ _ _ _ p q hpq :=
    truncationMap_pathProduct_stageKS hb hb0 ha ha0 (hx k) (hx (k + 1))
      (CompletedGroup.map_projection k (k + 1) (Nat.le_succ k) x) _ _
      (by simp only [Nat.even_add_one, decide_not]) p q hpq

/-- The diagram of the completed diagram at cutoff `k` is the stage of the parity of `k`. -/
@[simp]
theorem alternating_diagram (x : d.completedBCHGroup ℒ)
    (hx : ∀ k, CompletedGroup.projection k x ∈ hyperplaneLabels j h d ℒ b k) (k : ℕ) :
    (alternating hb hb0 ha ha0 x hx).diagram k =
      stageKS hb hb0 ha ha0 (CompletedGroup.projection k x) (hx k) (decide (Even k)) := (rfl)

end Diagram

section Orthant

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  (ℒ : (Fin 2 → ℤ) → Submodule R L) [GradedLieAlgebra ℒ]
  [IsPositiveGrading (PositiveDegrees.orthant (Fin 2)) ℒ]

local notation "Λ₂" => TauCeti.Toric.isIntegralLattice_compLeft_castAddHom (Fin 2)

/-- For `N = ℤ²` and `P = ℕ²`, a completed diagram whose complexes do not stabilize, built
from any completed group element `x` whose projections lie in the group of the Lie algebra
orthogonal to the hyperplane `θ ↦ θ(e₂) = 0`: the complex of the even cutoffs is cut out by
that hyperplane and the complex of the odd cutoffs by it and `θ(e₁) = 0`. -/
theorem exists_completedDiagram_not_eventually_eq_orthant
    (x : (PositiveDegrees.orthant (Fin 2)).completedBCHGroup ℒ)
    (hx : ∀ k, CompletedGroup.projection k x ∈ hyperplaneLabels
      ((Int.castAddHom ℝ).compLeft (Fin 2)) Λ₂
      (PositiveDegrees.orthant (Fin 2)) ℒ (Pi.single 1 1) k) :
    ∃ (C : ℕ → FinitePolyhedralComplex (Λ₂).continuousDual)
      (_ : CompletedDiagram (KSSpace.continuousDual Λ₂) (PositiveDegrees.orthant (Fin 2)) ℒ C),
      ¬∃ n, ∀ k ≥ n, C k = C (k + 1) := by
  have hmem (i : Fin 2) :
      (Pi.single i 1 : Fin 2 → ℤ) ∈ (PositiveDegrees.orthant (Fin 2)).monoid := by
    rw [PositiveDegrees.mem_orthant_monoid]
    intro i'
    by_cases hi : i' = i <;> simp [hi]
  have hne (i : Fin 2) : (Pi.single i 1 : Fin 2 → ℤ) ≠ 0 := by
    simp [Pi.single_eq_zero_iff]
  refine ⟨alternatingComplex Λ₂ (Pi.single 0 1) (Pi.single 1 1),
    alternating (hmem 1) (hne 1) (hmem 0) (hne 0) x hx,
    not_eventually_alternatingComplex_eq
      ((Λ₂).apply_ne_zero (hne 1))
      ⟨ContinuousLinearMap.proj 0, by simp, by simp⟩⟩

end Orthant

end Mei.CompletedDiagram
