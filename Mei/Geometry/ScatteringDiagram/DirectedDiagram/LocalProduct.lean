/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Chamber
public import Mei.Geometry.Convex.Polyhedron.Path.Subdivision
import Mei.Combinatorics.Quiver.Path

/-!
# Directed transport from local crossing formulas

Fix a cutoff `k` and a function `F` on the ambient space with values in the order-`k`
BCH group. Suppose that `F` is locally constant off the active supports and that at every
regular point `θ` and every velocity `v` transverse to the walls through `θ`,
`F (θ + s • v) * (F (θ - s • v))⁻¹` is the combined label of the wall germ at `θ` for all
small `s > 0`. Then every admissible path from `x` to `y` has order-`k` product
`F y * (F x)⁻¹`; in particular the diagram is consistent at order `k`.

This is the directed analogue of the local criterion for finite wall diagrams
(`FiniteWallDiagram.consistent_of_local`). Coincident and repeated
supports are allowed: the germ condition concerns the combined label of all active walls
through `θ`.

Conversely, the transport from a base point of a diagram consistent at order `k`, extended by
`1` to the active supports (`DirectedDiagram.levelTransportFun`), is such a function
(`DirectedDiagram.eventually_levelTransportFun_eq` and
`DirectedDiagram.eventually_levelTransportFun_mul_inv_eq`). Its values lie in every subgroup
containing the active projected labels, so the transports of two diagrams whose labels commute
commute (`DirectedDiagram.commute_levelTransportFun`).
-/

public section

open TauCeti (WallComplement AdmissiblePLPath singularSupport)

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Subdividing a polygonal path by allowed interior vertices preserves its order-`k`
transport. -/
theorem levelPathProduct_eq_of_isSubdivision (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {p q : AdmissiblePLPath x y} (hpq : p.IsSubdivision q) :
    D.levelPathProduct k q = D.levelPathProduct k p := by
  rw [D.levelPathProduct_eq_wallPathProduct k q (D.activeLabels_commute k),
    D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
  exact Quiver.Path.wallPathProduct_eq_of_signedCrossingEvents_eq _ _
    (D.activeLabels_commute k) q p (hpq.signedCrossingEvents_eq _)

variable (k : ℕ) {F : V → d.truncatedGroup ℒ k}

/-- A segment with at most one crossing time has transport `F y * (F x)⁻¹` when `F` satisfies
the local crossing formulas. -/
theorem levelPathProduct_toPath_eq_mul_inv_of_local
    (hF : ∀ θ, (∀ j : D.active k, θ ∉ (D.wall j).support) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ θ (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
      (v : V), (∀ j : D.active k, θ ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal v ≠ 0) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), F (θ + s • v) * (F (θ - s • v))⁻¹ = D.combinedLabel k θ v hθ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)} (e : x ⟶ y)
    (he : (Prod.snd '' WallComplement.crossings x y).Subsingleton) :
    D.levelPathProduct k e.toPath = F y.val * (F x.val)⁻¹ := by
  rcases (WallComplement.crossings x y).eq_empty_or_nonempty with hempty | ⟨⟨j₀, t⟩, ht⟩
  · rw [D.levelPathProduct_eq_one_of_crossings_eq_empty k e hempty,
      WallComplement.apply_eq_of_crossings_eq_empty hF hempty, mul_inv_cancel]
  -- All crossings occur at the single parameter `t`, at the point `θ`.
  have htI := ((WallComplement.mem_crossings _ _ _ _).mp ht).1
  have htIoo := WallComplement.mem_Ioo_of_mem_crossings ht
  set θ := AffineMap.lineMap x.val y.val t with hθ_def
  have hθ := e.down.regular t htI
  rw [D.levelPathProduct_toPath_eq_combinedLabel k e θ hθ t
    (WallComplement.mem_crossings_iff_of_subsingleton he ht)]
  have hv : ∀ j : D.active k, θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal (y.val - x.val) ≠ 0 := by
    intro j hj hzero
    apply e.down.transverse j ⟨t, htI, hj⟩
    rw [(D.wall j).direction_support]
    exact hzero
  -- Choose a small parameter `s` with `t ± s` inside the segment.
  obtain ⟨s, hs, hspos, hst⟩ := ((hcross θ hθ _ hv).and
    (Ioo_mem_nhdsGT (lt_min htIoo.1 (sub_pos.mpr htIoo.2)))).exists
  have hline (r : ℝ) : AffineMap.lineMap x.val y.val (t + r) = θ + r • (y.val - x.val) := by
    simp only [hθ_def, AffineMap.lineMap_apply_module']
    module
  obtain ⟨hx, hy⟩ := WallComplement.apply_eq_lineMap_of_subsingleton hF he ht hspos
    (hst.le.trans (min_le_left _ _)) (hst.le.trans (min_le_right _ _))
  have hminus : AffineMap.lineMap x.val y.val (t - s) = θ - s • (y.val - x.val) := by
    rw [sub_eq_add_neg t, hline, neg_smul, ← sub_eq_add_neg]
  rw [hx, ← hy, hminus, hline, hs]

/-- If `F` is locally constant off the active supports and satisfies the local crossing
formulas at every regular wall germ, then every admissible path from `x` to `y` has
order-`k` transport `F y * (F x)⁻¹`. -/
theorem levelPathProduct_eq_mul_inv_of_local
    (hF : ∀ θ, (∀ j : D.active k, θ ∉ (D.wall j).support) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ θ (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
      (v : V), (∀ j : D.active k, θ ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal v ≠ 0) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), F (θ + s • v) * (F (θ - s • v))⁻¹ = D.combinedLabel k θ v hθ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k p = F y.val * (F x.val)⁻¹ := by
  obtain ⟨q, hq, hsmall⟩ := p.exists_subdivision_subsingleton_crossingTimes
  rw [← D.levelPathProduct_eq_of_isSubdivision k hq]
  clear hq p
  induction q with
  | nil => simp
  | @cons y z q f ih =>
    rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.isChain_vertices_comp] at hsmall
    have hf : (Prod.snd '' WallComplement.crossings y z).Subsingleton := by
      simpa only [Quiver.Path.vertices_toPath, List.isChain_pair] using hsmall.2
    rw [D.levelPathProduct_cons, ih hsmall.1,
      D.levelPathProduct_toPath_eq_mul_inv_of_local k hF hcross f hf]
    group

/-- Local crossing formulas for a function `F` at every regular wall germ imply consistency
at order `k`. -/
theorem levelConsistent_of_local
    (hF : ∀ θ, (∀ j : D.active k, θ ∉ (D.wall j).support) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ θ (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
      (v : V), (∀ j : D.active k, θ ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal v ≠ 0) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), F (θ + s • v) * (F (θ - s • v))⁻¹ = D.combinedLabel k θ v hθ) :
    D.LevelConsistent k :=
  (D.levelConsistent_iff_loops k).mpr fun _ p => by
    rw [D.levelPathProduct_eq_mul_inv_of_local k hF hcross p, mul_inv_cancel]

section Transport

variable {k} (hD : D.LevelConsistent k)
  (x : WallComplement (fun j : D.active k => (D.wall j).support))

open scoped Classical in
/-- The order-`k` transport from `x` of a diagram consistent at order `k`, as a function on the
ambient space: `levelTransport k hD x y` at a point `y` off the active walls, and `1` on the
active walls. -/
def levelTransportFun (y : V) : d.truncatedGroup ℒ k :=
  if hy : ∀ j : D.active k, y ∉ (D.wall j).support then D.levelTransport k hD x ⟨y, hy⟩ else 1

/-- Off the active walls, the transport function is the endpoint transport. -/
theorem levelTransportFun_of_notMem {y : V} (hy : ∀ j : D.active k, y ∉ (D.wall j).support) :
    D.levelTransportFun hD x y = D.levelTransport k hD x ⟨y, hy⟩ := by
  classical
  rw [levelTransportFun]
  exact dite_eq_left hy

/-- At an allowed endpoint, the transport function is the endpoint transport. -/
theorem levelTransportFun_val (y : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.levelTransportFun hD x y.val = D.levelTransport k hD x y :=
  D.levelTransportFun_of_notMem hD x y.notMem

/-- On the active walls, the transport function is `1`. -/
theorem levelTransportFun_of_mem {y : V} (hy : ¬ ∀ j : D.active k, y ∉ (D.wall j).support) :
    D.levelTransportFun hD x y = 1 := by
  classical
  rw [levelTransportFun]
  exact dite_eq_right hy

/-- The transport function takes values in every subgroup containing the projected labels of
the walls active at order `k`. -/
theorem levelTransportFun_mem {S : Subgroup (d.truncatedGroup ℒ k)}
    (hS : ∀ j : D.active k, CompletedGroup.projection k (D.wall j).label ∈ S) (y : V) :
    D.levelTransportFun hD x y ∈ S := by
  by_cases hy : ∀ j : D.active k, y ∉ (D.wall j).support
  · obtain ⟨p⟩ := D.exists_level_path k x ⟨y, hy⟩
    rw [D.levelTransportFun_of_notMem hD x hy, D.levelTransport_eq_levelPathProduct hD p]
    exact D.levelPathProduct_mem k hS p
  · rw [D.levelTransportFun_of_mem hD x hy]
    exact S.one_mem

/-- Off the active walls, the transport function is locally constant. -/
theorem eventually_levelTransportFun_eq {θ : V} (hθ : ∀ j : D.active k, θ ∉ (D.wall j).support) :
    ∀ᶠ φ in 𝓝 θ, D.levelTransportFun hD x φ = D.levelTransportFun hD x θ := by
  have hopen := D.isOpen_setOf_forall_notMem_support k
  have hlc : ∀ᶠ φ in 𝓝[{z : V | ∀ j : D.active k, z ∉ (D.wall j).support}] θ,
      ∀ hφ, D.levelTransport k hD x ⟨φ, hφ⟩ = D.levelTransport k hD x ⟨θ, hθ⟩ :=
    (eventually_nhds_subtype_iff {z : V | ∀ j : D.active k, z ∉ (D.wall j).support} ⟨θ, hθ⟩
      (fun φ => ∀ hφ, D.levelTransport k hD x ⟨φ, hφ⟩ = D.levelTransport k hD x ⟨θ, hθ⟩)).mp
      (((D.isLocallyConstant_levelTransport hD x).eventually_eq ⟨θ, hθ⟩).mono
        fun _ hy _ => hy)
  rw [hopen.nhdsWithin_eq hθ] at hlc
  filter_upwards [hlc, hopen.mem_nhds hθ] with φ hφ hφU
  rw [D.levelTransportFun_of_notMem hD x hφU, D.levelTransportFun_of_notMem hD x hθ]
  exact hφ hφU

/-- At a point `θ` outside the singular support of the active walls and a velocity `v`
transverse to the active walls through `θ`, the transport function changes by the combined
label: `F (θ + s • v) * (F (θ - s • v))⁻¹` is the combined label for all small `s > 0`. -/
theorem eventually_levelTransportFun_mul_inv_eq {θ : V}
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) (v : V)
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), D.levelTransportFun hD x (θ + s • v) *
      (D.levelTransportFun hD x (θ - s • v))⁻¹ = D.combinedLabel k θ v hθ := by
  filter_upwards [D.eventually_exists_levelPathProduct_eq_combinedLabel k θ v hθ hv]
    with s ⟨ym, yp, e, hm, hp, he⟩
  rw [← hm, ← hp, D.levelTransportFun_val, D.levelTransportFun_val, ← he,
    ← D.levelTransport_eq_levelPathProduct hD e.toPath, D.levelTransport_comp hD x ym yp,
    mul_inv_cancel_right]

/-- If every projected label of `D` commutes with every projected label of `E` at order `k`,
the transport functions of `D` and `E` take commuting values. -/
theorem commute_levelTransportFun {κ : Type*} {E : DirectedDiagram (d := d) h H κ}
    (hE : E.LevelConsistent k) (x' : WallComplement (fun j : E.active k => (E.wall j).support))
    (hDE : ∀ a b, Commute (CompletedGroup.projection k (D.wall a).label)
      (CompletedGroup.projection k (E.wall b).label)) (y z : V) :
    Commute (D.levelTransportFun hD x y) (E.levelTransportFun hE x' z) := by
  have hy : D.levelTransportFun hD x y ∈
      Subgroup.centralizer (Set.range fun b : E.active k =>
        CompletedGroup.projection k (E.wall b).label) :=
    D.levelTransportFun_mem hD x (fun a => Subgroup.mem_centralizer_iff.mpr <| by
      rintro _ ⟨b, rfl⟩
      exact (hDE a b).symm.eq) y
  have hz : E.levelTransportFun hE x' z ∈
      Subgroup.centralizer {D.levelTransportFun hD x y} :=
    E.levelTransportFun_mem hE x' (fun b => Subgroup.mem_centralizer_iff.mpr <| by
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.mp hy _ ⟨b, rfl⟩).symm) z
  exact Subgroup.mem_centralizer_iff.mp hz _ rfl

end Transport

end Mei.DirectedDiagram
