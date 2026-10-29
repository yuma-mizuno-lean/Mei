/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Graph
public import Mei.Geometry.ScatteringDiagram.WallSpace.Hom

/-!
# Directed wall spaces on graph degrees

Reindex directed wall spaces along `n ↦ (f n, n)`, extending them by zero off
the graph. The spatial map on the larger degree group can be any additive map
agreeing with the original directions on the graph. Thus graph reindexing can
retain either the full principal direction or its spatial projection.

The graph lift of each supported ray retains its actual allowed degrees. The
existing `PositiveDegrees.graphBCHGroupEquiv` restricts to an equivalence of its
wall groups, with the same cutoff orders and integral normals. No saturation,
freeness or injectivity of the spatial map is needed.

We reuse `graphGrading`, `SupportedRay.graph` and the wall-preservation theorem
`GradedLieHom.completedMap_mem_wallGroup`. The subgroup restriction follows the
construction of `DirectedWallSpaces.CoordinateChange.wallGroupEquiv`.
-/

public section

noncomputable section

namespace Mei.DirectedWallSpaces

variable {Γ M Λ R L : Type*} [AddCommMonoid Γ] [AddCommMonoid M] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}
  (H : DirectedWallSpaces ρ ℒ) (f : Γ →+ M) (ρ' : M × Γ →+ Λ)
  (hρ : ∀ n, ρ' (f n, n) = ρ n)

/-- Reindex homogeneous wall spaces on graph degrees. Only the directions on the
graph matter; all off-graph wall spaces vanish. -/
def graph : DirectedWallSpaces ρ' (graphGrading ℒ f) where
  wall p m := graphGrading (fun n => H.wall n m) f p
  wall_le_piece := by
    rintro ⟨a, n⟩ m
    by_cases ha : a = f n
    · subst a
      simpa only [graphGrading_apply] using H.wall_le_piece n m
    · rw [graphGrading_eq_bot _ _ (p := (a, n)) ha,
        graphGrading_eq_bot _ _ (p := (a, n)) ha]
  zero_normal p := by
    simp only [graphGrading_def, H.zero_normal, ite_self]
  nontangent := by
    rintro ⟨a, n⟩ m hm
    by_cases ha : a = f n
    · subst a
      rw [graphGrading_apply, H.nontangent n m (by simpa only [hρ] using hm)]
    · exact graphGrading_eq_bot _ _ ha
  rescale p m c hc := by
    simp only [graphGrading_def, H.rescale _ m c hc]
  bracket_mem := by
    rintro ⟨a, n⟩ ⟨b, n'⟩ m m' x y hx hy
    by_cases ha : a = f n
    · by_cases hb : b = f n'
      · subst a b
        rw [graphGrading_apply] at hx hy
        have he : wallBracketNormal ρ' (f n, n) (f n', n') m m' =
            wallBracketNormal ρ n n' m m' := by
          ext v
          simp only [wallBracketNormal_apply, hρ]
        simpa only [Prod.mk_add_mk, ← map_add, graphGrading_apply, he] using
          H.bracket_mem hx hy
      · rw [graphGrading_eq_bot _ _ hb, Submodule.mem_bot] at hy
        simp only [hy, lie_zero, Submodule.zero_mem]
    · rw [graphGrading_eq_bot _ _ ha, Submodule.mem_bot] at hx
      simp only [hx, zero_lie, Submodule.zero_mem]

/-- The reindexed wall family is the graph reindexing of the original family. -/
theorem graph_wall (p : M × Γ) (m : Λ →+ ℤ) :
    (H.graph f ρ' hρ).wall p m = graphGrading (fun n => H.wall n m) f p := (rfl)

/-- At a graph degree, the original homogeneous wall space is retained exactly. -/
@[simp]
theorem graph_wall_apply (n : Γ) (m : Λ →+ ℤ) :
    (H.graph f ρ' hρ).wall (f n, n) m = H.wall n m := by
  rw [graph_wall, graphGrading_apply]

/-- Off the graph no homogeneous wall elements are introduced. -/
@[simp]
theorem graph_wall_eq_bot {p : M × Γ} (hp : p.1 ≠ f p.2) (m : Λ →+ ℤ) :
    (H.graph f ρ' hρ).wall p m = ⊥ := by
  rw [graph_wall, graphGrading_eq_bot _ _ hp]

end Mei.DirectedWallSpaces

namespace Mei.DirectedWallSpaces

variable {Γ M Λ R L : Type*} [AddCommGroup Γ] [AddCommGroup M] [AddCommMonoid Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [DecidableEq M]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (f : Γ →+ M) (ρ' : M × Γ →+ Λ)
  (hρ : ∀ n, ρ' (f n, n) = ρ n)

/-- Graph reindexing preserves and reflects membership of completed wall labels,
at the graph lift of the supported primitive ray. -/
theorem graphBCHGroupEquiv_mem_wallGroup_iff (w : SupportedRay d) (m : Λ →+ ℤ)
    (g : d.completedBCHGroup ℒ) :
    d.graphBCHGroupEquiv ℒ f g ∈ (H.graph f ρ' hρ).wallGroup (w.graph f) m ↔
      g ∈ H.wallGroup w m := by
  constructor
  · intro hg
    have h := (graphProjectionGradedLieHom ℒ f d).completedMap_mem_wallGroup
      (H := H.graph f ρ' hρ) (H' := H) (w := w.graph f) (v := w) (m := m) (m' := m)
      (fun p hp => by
        simpa only [PositiveDegrees.graphProjection_apply] using
          ((w.mem_graph_rayDegrees f p.1 p.2).mp hp).1)
      (fun p _ x hx => by
        simpa only [graphProjectionGradedLieHom_apply, PositiveDegrees.graphProjection_apply]
          using graphGrading_le (fun n => H.wall n m) f p hx) hg
    rw [← PositiveDegrees.graphBCHGroupEquiv_symm_apply, MulEquiv.symm_apply_apply] at h
    exact h
  · intro hg
    rw [PositiveDegrees.graphBCHGroupEquiv_apply]
    exact (graphGradedLieHom ℒ f d).completedMap_mem_wallGroup
      (fun n hn => by simpa using hn)
      (fun n _ x hx => by simpa using hx) hg

/-- The graph comparison carries each completed wall subgroup onto the wall
subgroup at its lifted ray, retaining the integral normal. -/
theorem map_graph_wallGroup (w : SupportedRay d) (m : Λ →+ ℤ) :
    (H.wallGroup w m).map (d.graphBCHGroupEquiv ℒ f : _ →* _) =
      (H.graph f ρ' hρ).wallGroup (w.graph f) m := by
  ext g
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv]
  simpa only [MulEquiv.apply_symm_apply] using
    (H.graphBCHGroupEquiv_mem_wallGroup_iff f ρ' hρ w m
      ((d.graphBCHGroupEquiv ℒ f).symm g)).symm

/-- Restrict graph regrading to an equivalence of completed wall groups. -/
def graphWallGroupEquiv (w : SupportedRay d) (m : Λ →+ ℤ) :
    H.wallGroup w m ≃* (H.graph f ρ' hρ).wallGroup (w.graph f) m :=
  ((d.graphBCHGroupEquiv ℒ f).subgroupMap (H.wallGroup w m)).trans
    (MulEquiv.subgroupCongr (H.map_graph_wallGroup f ρ' hρ w m))

/-- On labels the wall-group comparison is the ambient graph comparison. -/
@[simp]
theorem coe_graphWallGroupEquiv_apply (w : SupportedRay d) (m : Λ →+ ℤ)
    (g : H.wallGroup w m) :
    (H.graphWallGroupEquiv f ρ' hρ w m g :
      (d.graph f).completedBCHGroup (graphGrading ℒ f)) =
      d.graphBCHGroupEquiv ℒ f g := (rfl)

/-- The inverse wall-group comparison is the inverse ambient graph comparison. -/
@[simp]
theorem coe_graphWallGroupEquiv_symm_apply (w : SupportedRay d) (m : Λ →+ ℤ)
    (g : (H.graph f ρ' hρ).wallGroup (w.graph f) m) :
    ((H.graphWallGroupEquiv f ρ' hρ w m).symm g : d.completedBCHGroup ℒ) =
      (d.graphBCHGroupEquiv ℒ f).symm g := by
  apply (d.graphBCHGroupEquiv ℒ f).injective
  rw [← coe_graphWallGroupEquiv_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Mei.DirectedWallSpaces
