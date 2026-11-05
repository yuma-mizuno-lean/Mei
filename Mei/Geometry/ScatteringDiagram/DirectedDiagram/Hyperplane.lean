/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Invariance
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane

/-!
# A single full hyperplane is consistent but not equivalent to the empty diagram

The finite-order transport of a directed diagram with one wall whose support is a full affine
hyperplane `{ℓ = c}`, `ℓ` the real extension of the wall normal, is
`θ ^ (side x - side y)`, where `θ` is the projected label and `side z` is one on `{ℓ > c}` and
zero otherwise. Every closed path has trivial transport, so the diagram is consistent at every
order. When the label is not the identity, the transport between points on the two sides is a
nonidentity element, whereas a diagram without walls has trivial transport. Hence the diagram is
not equivalent to any diagram without walls: consistency does not force a diagram to be
equivalent to the empty one.

More generally, any diagram of full affine hyperplanes whose labels commute pairwise is
consistent, at each order where its active projected labels commute; in particular this holds
for every diagram of full hyperplanes over an abelian Lie algebra. The coefficient Lie algebra
of the zero skew form is such an algebra.

If all walls share one full affine hyperplane as support, every point is regular for the walls
active at every order (`DirectedDiagram.notMem_singularSupport_of_support_eq`): the hyperplane has
empty relative boundary.

The commutative hyperplane transport `Quiver.Path.wallPathProduct_eq_prod_of_hyperplanes` is
applied to the abelian group of integer powers of the label, which is mapped into the truncated
group by `zpowersHom`. For commuting labels it is applied in the commutative subgroup generated
by the active labels (`Subgroup.isMulCommutative_closure`).
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

section Empty

variable (D : DirectedDiagram (d := d) h H ι)

/-- A diagram with no wall active at order `k` has trivial order-`k` transport along every
admissible path. -/
@[simp]
theorem levelPathProduct_of_isEmpty_active (k : ℕ) [IsEmpty (D.active k)]
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) : D.levelPathProduct k p = 1 := by
  induction p with
  | nil => exact D.levelPathProduct_nil k _
  | cons p e ih =>
    rw [D.levelPathProduct_cons, ih, mul_one]
    exact D.levelPathProduct_eq_one_of_crossings_eq_empty k e (Set.eq_empty_of_isEmpty _)

/-- A diagram without walls is consistent. -/
theorem consistent_of_isEmpty [IsEmpty ι] : D.Consistent :=
  D.consistent_iff_loops.mpr fun k _ p => D.levelPathProduct_of_isEmpty_active k p

/-- A diagram without walls has trivial completed transport. -/
theorem transport_of_isEmpty [IsEmpty ι] (x y : D.Point) :
    D.transport D.consistent_of_isEmpty x y = 1 := by
  apply CompletedGroup.ext
  intro k
  obtain ⟨p⟩ := D.exists_level_path k (CommonWallComplement.projection k x)
    (CommonWallComplement.projection k y)
  rw [D.projection_transport D.consistent_of_isEmpty k p]
  exact (D.levelPathProduct_of_isEmpty_active k p).trans (map_one _).symm

end Empty

section Hyperplane

variable {D : DirectedDiagram (d := d) h H ι} [Unique ι]
  {W : DirectedWall (d := d) h H} (hD : ∀ j, D.wall j = W) (c : ℝ)

include hD in
/-- The finite-order transport of a diagram whose single indexed wall is `W`, with support the
full affine hyperplane `{ℓ = c}` for the real extension `ℓ` of its normal, is the power
`θ ^ (side x - side y)` of the projected label `θ`, where `side z` is one if `c < ℓ z` and zero
otherwise. -/
theorem levelPathProduct_eq_zpow_of_support_eq
    (hW : W.support = {z | h.realCharacter W.normal z = c}) (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k p =
      CompletedGroup.projection k W.label ^
        ((if c < h.realCharacter W.normal x.val then 1 else 0 : ℤ) -
          (if c < h.realCharacter W.normal y.val then 1 else 0 : ℤ)) := by
  classical
  by_cases hθ : CompletedGroup.projection k W.label = 1
  · have hempty : IsEmpty (D.active k) :=
      ⟨fun j => (D.mem_active k j.1).mp j.2 (by rw [hD]; exact hθ)⟩
    refine (D.levelPathProduct_of_isEmpty_active k p).trans (Eq.symm ?_)
    rw [hθ]
    exact one_zpow _
  · let j₀ : D.active k := ⟨default, (D.mem_active k _).mpr (by rw [hD]; exact hθ)⟩
    let := Fintype.ofFinite (D.active k)
    let F : D.active k → (V →ᵃ[ℝ] ℝ) := fun _ =>
      (h.realCharacter W.normal).toAffineMap - AffineMap.const ℝ V c
    have hF : ∀ j, (F j).linear = h.realCharacter W.normal := fun j => by
      ext z
      simp [F]
    have hsupp : ∀ j : D.active k, (D.wall j).support = {z | F j z = 0} := fun j => by
      ext z
      simp [F, hD, hW, sub_eq_zero]
    have hp := p.wallPathProduct_eq_prod_of_hyperplanes F
      (fun _ : D.active k => Multiplicative.ofAdd (1 : ℤ))
      (fun j _ => hsupp j)
    have hmap := p.map_wallPathProduct (fun j => (F j).linear)
      (fun _ : D.active k => Multiplicative.ofAdd (1 : ℤ))
      (fun _ _ _ => Commute.all _ _) (zpowersHom _ (CompletedGroup.projection k W.label))
    rw [hp, Fintype.prod_subsingleton _ j₀, map_zpow] at hmap
    have hν : (fun j => (F j).linear) =
        fun j : D.active k => h.realCharacter (D.wall j).normal := by
      funext j
      exact (hF j).trans (by rw [hD j.1])
    have hl : (fun _ : D.active k => CompletedGroup.projection k W.label) =
        fun j : D.active k => CompletedGroup.projection k (D.wall j).label := by
      funext j
      rw [hD j.1]
    have hside : ∀ z, 0 < F j₀ z ↔ c < h.realCharacter W.normal z := fun z => by
      simp [F, sub_pos]
    simp only [zpowersHom_apply, toAdd_ofAdd, zpow_one, hside] at hmap
    rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
    exact (p.wallPathProduct_congr hν.symm hl.symm).trans hmap.symm

include hD in
/-- A diagram whose single indexed wall is a full affine hyperplane `{ℓ = c}` is consistent,
whatever its label. -/
theorem consistent_of_support_eq (hW : W.support = {z | h.realCharacter W.normal z = c}) :
    D.Consistent :=
  D.consistent_iff_loops.mpr fun k _ p =>
    (D.levelPathProduct_eq_zpow_of_support_eq hD c hW k p).trans (by
      rw [sub_self]
      exact zpow_zero _)

include hD in
/-- A diagram whose single indexed wall is a full affine hyperplane `{ℓ = c}` with a nonidentity
label is not equivalent to any diagram without walls (see `consistent_of_support_eq`
for its consistency). -/
theorem not_equivalent_of_isEmpty_of_support_eq {κ : Type*} [IsEmpty κ]
    (E : DirectedDiagram (d := d) h H κ)
    (hW : W.support = {z | h.realCharacter W.normal z = c}) (hθ : W.label ≠ 1) :
    ¬ D.Equivalent E := by
  intro hDE
  have hℓ : h.realCharacter W.normal ≠ 0 := fun he => W.normal_ne_zero (by
    ext n
    simpa using DFunLike.congr_fun he (i n))
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hℓ
  set u : V := (h.realCharacter W.normal v)⁻¹ • v with hu_def
  have hu : h.realCharacter W.normal u = 1 := by
    simp only [hu_def, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ (by simpa using hv)
  have hpoint (t : ℝ) (ht : t ≠ c) (k : ℕ) (j : D.active k) :
      t • u ∉ (D.wall j).support := by
    rw [hD j.1, hW]
    simpa [hu] using ht
  let xD : D.Point := ⟨(c + 1) • u, fun k j => hpoint _ (by linarith) k j⟩
  let yD : D.Point := ⟨(c - 1) • u, fun k j => hpoint _ (by linarith) k j⟩
  let xE : E.Point := ⟨(c + 1) • u, fun _ j => isEmptyElim j.1⟩
  let yE : E.Point := ⟨(c - 1) • u, fun _ j => isEmptyElim j.1⟩
  have htrans := hDE.transport_eq (D.consistent_of_support_eq hD c hW) E.consistent_of_isEmpty
    (x := xD) (y := yD) (x' := xE) (y' := yE) rfl rfl
  rw [E.transport_of_isEmpty xE yE] at htrans
  obtain ⟨k, hk⟩ : ∃ k, CompletedGroup.projection k W.label ≠ 1 := by
    by_contra hcon
    exact hθ (CompletedGroup.ext fun k => by
      rw [not_not.mp fun hne => hcon ⟨k, hne⟩, map_one])
  obtain ⟨p⟩ := D.exists_level_path k (CommonWallComplement.projection k xD)
    (CommonWallComplement.projection k yD)
  have hproj := D.projection_transport (D.consistent_of_support_eq hD c hW) k p
  rw [htrans, map_one, D.levelPathProduct_eq_zpow_of_support_eq hD c hW k p] at hproj
  have hxc : c < c + 1 := by linarith
  have hyc : ¬ c < c - 1 := by linarith
  have hexp : CompletedGroup.projection k W.label ^ (1 : ℤ) = 1 := by
    simpa [xD, yD, hu, hxc, hyc] using hproj.symm
  exact hk (by simpa using hexp)

end Hyperplane

section Commuting

variable (D : DirectedDiagram (d := d) h H ι)

open scoped IsMulCommutative in
/-- Full affine hyperplanes whose projected labels commute pairwise are consistent at that
order. Hyperplanes may cross, coincide or repeat, and only the walls active at order `k` are
constrained. The labels are moved into the commutative subgroup they generate, where the
commutative hyperplane transport `Quiver.Path.wallPathProduct_loop_eq_one_of_hyperplanes`
applies. -/
theorem levelConsistent_of_commute_of_full (k : ℕ)
    (hfull : ∀ j : D.active k, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hcomm : ∀ a b : D.active k, Commute (CompletedGroup.projection k (D.wall a).label)
      (CompletedGroup.projection k (D.wall b).label)) :
    D.LevelConsistent k := by
  choose b hb using hfull
  let ℓ := fun j : D.active k => CompletedGroup.projection k (D.wall j).label
  let G := Subgroup.closure (Set.range ℓ)
  have : IsMulCommutative G := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩ _
    exact hcomm a c)
  let F : D.active k → (V →ᵃ[ℝ] ℝ) := fun j =>
    (h.realCharacter (D.wall j).normal).toAffineMap - AffineMap.const ℝ V (b j)
  let lab : D.active k → G := fun j => ⟨ℓ j, Subgroup.subset_closure (Set.mem_range_self j)⟩
  apply (D.levelConsistent_iff_loops k).mpr
  intro x p
  have hloop := p.wallPathProduct_loop_eq_one_of_hyperplanes F lab (fun j _ => by
    ext z
    simp [F, hb j, sub_eq_zero])
  have hmap := p.map_wallPathProduct (fun j => (F j).linear) lab
    (fun _ _ _ => Commute.all _ _) G.subtype
  rw [hloop, map_one] at hmap
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
  exact (p.wallPathProduct_congr (funext fun j => by ext z; simp [F]) rfl).trans hmap.symm

/-- Full affine hyperplanes with pairwise commuting completed labels form a consistent
diagram. -/
theorem consistent_of_commute_of_full
    (hfull : ∀ j, ∃ b : ℝ, (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hcomm : ∀ a b, Commute (D.wall a).label (D.wall b).label) :
    D.Consistent :=
  D.consistent_iff.mpr fun k => D.levelConsistent_of_commute_of_full k (fun j => hfull j)
    (fun a c => (hcomm a c).map (CompletedGroup.projection k))

/-- Over an abelian Lie algebra, every diagram of full affine hyperplanes is consistent:
all completed labels commute, by `PositiveDegrees.commute_of_lie_logComponent_eq_zero`. -/
theorem consistent_of_isLieAbelian_of_full [IsLieAbelian L]
    (hfull : ∀ j, ∃ b : ℝ, (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}) :
    D.Consistent :=
  D.consistent_of_commute_of_full hfull fun _ _ =>
    d.commute_of_lie_logComponent_eq_zero fun _ _ => trivial_lie_zero _ _ _ _

end Commuting

section Regular

variable (D : DirectedDiagram (d := d) h H ι)

/-- Suppose that all walls of `D` have the support of the wall `j₀`, and that this support is
the full affine hyperplane `{ℓ = c}` for the real extension `ℓ` of the normal of `j₀`. Then no
point is singular for the walls active at any order. Indeed, the hyperplane has empty relative
boundary, and all walls have the same affine direction. -/
theorem notMem_singularSupport_of_support_eq {j₀ : ι} {c : ℝ}
    (hj₀ : (D.wall j₀).support = {z | h.realCharacter (D.wall j₀).normal z = c})
    (hD : ∀ j, (D.wall j).support = (D.wall j₀).support) (k : ℕ) (θ : V) :
    θ ∉ singularSupport (fun j : D.active k => (D.wall j).support) := by
  have hfr : intrinsicFrontier ℝ (D.wall j₀).support = ∅ := by
    obtain ⟨x, hx⟩ := (D.wall j₀).support_nonempty
    have hpre : ((↑) : affineSpan ℝ (D.wall j₀).support → V) ⁻¹' (D.wall j₀).support =
        univ := by
      refine eq_univ_of_forall fun y => ?_
      have hyx : (y : V) - x ∈ LinearMap.ker (h.realCharacter (D.wall j₀).normal) := by
        rw [← (D.wall j₀).direction_support]
        exact AffineSubspace.vsub_mem_direction y.property (subset_affineSpan ℝ _ hx)
      rw [hj₀] at hx
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hyx
      exact (Set.ext_iff.mp hj₀ y).mpr (hyx.trans hx)
    rw [intrinsicFrontier, hpre, frontier_univ, image_empty]
  rw [mem_singularSupport]
  rintro (⟨j, hj⟩ | ⟨j, j', hne, -, -⟩)
  · rw [hD, hfr] at hj
    exact hj
  · exact hne (by rw [hD, hD j'])

end Regular

section AffineHyperplane

variable {D : DirectedDiagram (d := d) h H ι} [Unique ι] {m : Λ →+ ℤ} (hm : m ≠ 0) (c : ℝ)
  {w : SupportedRay d} (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m)
  (hD : ∀ j, D.wall j = DirectedWall.ofAffineHyperplane h H m hm c w hw g)

include hD in
/-- A diagram whose only wall is the full hyperplane `DirectedWall.ofAffineHyperplane`
is consistent. -/
theorem consistent_ofAffineHyperplane : D.Consistent :=
  D.consistent_of_support_eq hD c (by simp)

include hD in
/-- A diagram whose only wall is `DirectedWall.ofAffineHyperplane` with a nonidentity label is
consistent but not equivalent to any diagram without walls. -/
theorem not_equivalent_ofAffineHyperplane {κ : Type*} [IsEmpty κ]
    (E : DirectedDiagram (d := d) h H κ) (hg : (g : d.completedBCHGroup ℒ) ≠ 1) :
    ¬ D.Equivalent E :=
  D.not_equivalent_of_isEmpty_of_support_eq hD c E (by simp) (by simpa using hg)

end AffineHyperplane

end Mei.DirectedDiagram
