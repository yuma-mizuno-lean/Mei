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

The commutative hyperplane transport `Quiver.Path.wallPathProduct_eq_prod_of_hyperplanes` is
applied to the abelian group of integer powers of the label, which is mapped into the truncated
group by `zpowersHom`.
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
    -- Only `ν` and the labels enter `wallPathProduct`; the commutation proof is irrelevant.
    have hcongr : ∀ (ν₁ ν₂ : D.active k → V →ₗ[ℝ] ℝ) (l₁ l₂ : D.active k → d.truncatedGroup ℒ k)
        (hc₁ : ∀ a b : D.active k,
          affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support →
            Commute (l₁ a) (l₁ b))
        (hc₂ : ∀ a b : D.active k,
          affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support →
            Commute (l₂ a) (l₂ b)), ν₁ = ν₂ → l₁ = l₂ →
        p.wallPathProduct ν₁ l₁ hc₁ = p.wallPathProduct ν₂ l₂ hc₂ := by
      rintro _ _ _ _ _ _ rfl rfl
      rfl
    rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
    exact (hcongr _ _ _ _ _ _ hν.symm hl.symm).trans hmap.symm

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
  simp [xD, yD, hu, hxc, hyc] at hproj
  exact hk hproj.symm

end Hyperplane

section LinearHyperplane

variable {D : DirectedDiagram (d := d) h H ι} [Unique ι] {m : Λ →+ ℤ} (hm : m ≠ 0)
  {w : SupportedRay d} (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m)
  (hD : ∀ j, D.wall j = DirectedWall.ofLinearHyperplane h H m hm w hw g)

include hD in
/-- A diagram whose only wall is the linear hyperplane `DirectedWall.ofLinearHyperplane`
is consistent. -/
theorem consistent_ofLinearHyperplane : D.Consistent :=
  D.consistent_of_support_eq hD 0 (by ext; simp)

include hD in
/-- A diagram whose only wall is `DirectedWall.ofLinearHyperplane` with a nonidentity label is
consistent but not equivalent to any diagram without walls. -/
theorem not_equivalent_ofLinearHyperplane {κ : Type*} [IsEmpty κ]
    (E : DirectedDiagram (d := d) h H κ) (hg : (g : d.completedBCHGroup ℒ) ≠ 1) :
    ¬ D.Equivalent E :=
  D.not_equivalent_of_isEmpty_of_support_eq hD 0 E (by ext; simp) (by simpa using hg)

end LinearHyperplane

end Mei.DirectedDiagram
