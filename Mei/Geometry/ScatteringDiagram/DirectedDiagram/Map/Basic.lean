/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Map
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Completion

/-!
# Coefficient maps of directed scattering diagrams

A fixed-degree Lie homomorphism preserving wall spaces maps every indexed label.
The active wall family can shrink: a noninjective coefficient map may kill a
label. Consistency is preserved for all paths of the resulting diagram, including
those through supports that disappear. A coefficient endomorphism fixes the product
of a path in a convex region if it fixes the labels of the walls meeting that region.

The coefficient map is the special case `DirectedWall.Pushforward.ofFixedDegree` of
`DirectedDiagram.pushforward`, with identity spatial map, rays and normals, so path
transport and endpoint transport are the pushforward ones. Together with outgoingness
of mapped walls, this gives coefficient naturality of outgoing completions. No faithful
action or injective coefficient map is needed.
-/

public section

open TauCeti (WallComplement AdmissiblePLPath GradedLieHom)

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Λ R V ι : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'} {ℋ : Γ → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  {H'' : DirectedWallSpaces ρ ℋ}
  (D : DirectedDiagram (d := d) h H ι)
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m)

/-- Apply a fixed-degree coefficient map to every wall label, retaining its index. -/
def map : DirectedDiagram (d := d) h H' ι where
  wall j := (D.wall j).map f hf
  finite_active := by
    simpa only [DirectedWall.map_label] using f.hasFiniteSupport_completedMap D.finite_active

@[simp]
theorem map_wall (j : ι) : (D.map f hf).wall j = (D.wall j).map f hf := (rfl)

/-- Fixed-degree coefficient maps of diagrams are pushforwards. -/
@[simp]
theorem pushforward_ofFixedDegree :
    D.pushforward (DirectedWall.Pushforward.ofFixedDegree f hf) = D.map f hf := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- The identity pushforward fixes every directed diagram. -/
@[simp]
theorem pushforward_id : D.pushforward DirectedWall.Pushforward.id = D := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- The identity coefficient map fixes the indexed diagram. -/
@[simp]
theorem map_id : D.map (GradedLieHom.id ℒ) (fun _ _ _ hx => by simpa using hx) = D := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Successive coefficient maps agree with their composite on indexed diagrams. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (hg : ∀ n m, ∀ x ∈ H'.wall n m, g x ∈ H''.wall n m) :
    (D.map f hf).map g hg = D.map
      (g.compId f)
      (fun n m x hx => by
        simpa only [GradedLieHom.compId_apply] using hg n m _ (hf n m x hx)) := by
  apply DirectedDiagram.ext
  funext j
  simp only [map_wall, DirectedWall.map_map]

/-- A group endomorphism fixes the finite-order product of a path whose vertices
lie in a convex region, provided it fixes the order-`k` label of every active wall meeting that
region. Walls missing the region may have arbitrary labels. -/
theorem map_levelPathProduct_eq_self (k : ℕ)
    (F : d.truncatedGroup ℒ k →* d.truncatedGroup ℒ k) {U : Set V} (hU : Convex ℝ U)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (hp : ∀ z ∈ p.vertices, z.val ∈ U)
    (hF : ∀ j : D.active k, (U ∩ (D.wall j).support).Nonempty →
      F (TauCeti.CompletedGroup.projection k (D.wall j).label) =
        TauCeti.CompletedGroup.projection k (D.wall j).label) :
    F (D.levelPathProduct k p) = D.levelPathProduct k p := by
  let ν := fun j : D.active k => h.realCharacter (D.wall j).normal
  -- Read the tower projections as elements of the concrete finite BCH group.
  let c : D.active k → d.truncatedGroup ℒ k := fun j => TauCeti.CompletedGroup.projection k (D.wall j).label
  let l := (p.signedCrossingEvents ν).reverse.flatMap Finset.toList
  have hl : l.map (fun a => F (c a.1) ^ a.2) = l.map (fun a => c a.1 ^ a.2) := by
    apply List.map_congr_left
    intro a ha
    obtain ⟨S, hS, haS⟩ := List.mem_flatMap.mp ha
    have hne := p.inter_nonempty_of_mem_signedCrossingEvents _ hU hp (List.mem_reverse.mp hS)
      (Finset.mem_toList.mp haS)
    rw [hF a.1 hne]
  have hm : F (p.wallPathProduct ν c (D.activeLabels_commute k)) =
      p.wallPathProduct ν (fun j => F (c j))
        (fun a b hab => (D.activeLabels_commute k a b hab).map F) :=
    p.map_wallPathProduct ν c (D.activeLabels_commute k) F
  rw [Quiver.Path.wallPathProduct_eq_prod_flatMap, hl,
    ← Quiver.Path.wallPathProduct_eq_prod_flatMap ν c (D.activeLabels_commute k)] at hm
  exact (congrArg F (D.levelPathProduct_eq_wallPathProduct k p _)).trans
    (hm.trans (D.levelPathProduct_eq_wallPathProduct k p _).symm)

/-- Coefficient maps preserve consistency even though paths may cross supports
of labels killed by the map. -/
theorem LevelConsistent.map {k : ℕ} (hD : D.LevelConsistent k) :
    (D.map f hf).LevelConsistent k := by
  rw [← pushforward_ofFixedDegree]
  exact hD.pushforward (by simp)

/-- A consistent directed diagram remains consistent after changing coefficients. -/
theorem Consistent.map (hD : D.Consistent) : (D.map f hf).Consistent := by
  rw [← pushforward_ofFixedDegree]
  exact hD.pushforward

omit D in
/-- Mapping coefficients sends an outgoing completion to an outgoing completion
of the mapped input, even when some initial or outgoing labels vanish. -/
theorem IsOutgoingCompletion.map {ι₀ κ : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H}
    {E : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)}
    (hE : IsOutgoingCompletion D₀ E) :
    IsOutgoingCompletion (fun j => (D₀ j).map f hf) (E.map f hf) := by
  simp_rw [← DirectedWall.pushforward_ofFixedDegree, ← pushforward_ofFixedDegree]
  exact hE.pushforward

omit D in
/-- Every outgoing completion of the mapped input represents the coefficient
image of any outgoing completion of the original input. -/
theorem IsOutgoingCompletion.equivalent_map {ι₀ κ κ' : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H}
    {E : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)}
    {E' : DirectedDiagram (d := d) h H' (ι₀ ⊕ κ')}
    (hE : IsOutgoingCompletion D₀ E)
    (hE' : IsOutgoingCompletion (fun j => (D₀ j).map f hf) E') :
    E'.Equivalent (E.map f hf) :=
  outgoingCompletion_unique hE' (hE.map f hf)

end Mei.DirectedDiagram
