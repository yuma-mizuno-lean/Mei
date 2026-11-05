/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Equivalence
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Specialization
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Completion
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Scat
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.WallFunction
public import Mei.Algebra.MonoidAlgebra.Range

/-!
# Function-wall groupings under pushforward

Let `P` be `DirectedWall.Pushforward` data over a positive degree map `T`, and let spatial
projections `π : Γ → M` and `π' : Γ' → M` satisfy `π' ∘ T = π` on allowed degrees. The projected
generator of a wall is then positively proportional to the projected generator of the pushed
wall (`DirectedWall.exists_nsmul_projection_pushforward_ray_generator`). Hence a function-wall
grouping of a diagram `D` is a grouping of `D.pushforward P`
(`DirectedDiagram.FunctionWallGrouping.pushforward`), provided the normal map keeps the normals
of the walls primitive: supports move by the spatial map and normals by the normal map, both
uniformly in each group. The completed label of a pushed group is the image of the completed
group label under the completed Lie map (`FunctionWallGrouping.label_pushforward`).

For the finite-index pushforward `DirectedWall.Pushforward.ofFiniteIndex`, where the normal `n`
of a group goes to `ν n` with `ν n ∘ t = q n • n`, the theorem
`FunctionWallGrouping.label_pushforward_ofFiniteIndex` transports a given group label. Assume
that `π' ∘ T = π` on allowed degrees, that the pushed normals of the walls are primitive, that
the group has the function-wall label `exp(log(f₀) ∂_n)`, that `q n = r` and that
`T_* f₀ = f₁ ^ r`. Then the pushed group has the label `exp(log(f₁) ∂_{n'})` for any integral
normal `n'` with `n' ∘ t = q n • n`, for instance `ν n`. The proof applies
`Mei.DirectedWall.Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog` to
the group label. Crossing germs of a group are carried to crossing germs of the pushed group by
the spatial map (`FunctionWallGrouping.IsCrossingGerm.pushforward`). Hence a diagram equivalent
to the pushforward has the same label `exp(log(f₁) ∂_{n'})` on any group whose crossing germs at
every order are the images of crossing germs of the source group
(`FunctionWallGrouping.label_eq_of_equivalent_pushforward_ofFiniteIndex`), by
`FunctionWallGrouping.label_eq_of_equivalent`. The source group and its label
`exp(log(f₀) ∂_n)` with `T_* f₀ = f₁ ^ r`, and the crossing germs of both groups, are
hypotheses. The lattice change
is motivated by Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
Theorem 9.5 (arXiv:2503.03719v1).

## Positivity under pushforward

Let `Φ` be a map of completed coefficient algebras `A[[Q]] → A'[[Q']]` intertwining the actions
along the completed Lie map of `P`, sending each monomial `z^p` to `z^{τ p}` for a surjection
`τ : Q → Q'`, and such that the target action fixes the constants of `A'`. If the normal map
of `P` preserves the pairings of the wall normals with `Q`, then `Φ` sends wall functions of
groups to wall functions of the pushed groups
(`DirectedDiagram.FunctionWallGrouping.IsWallFunction.pushforward`), by
`DirectedDiagram.FunctionWallGrouping.IsWallFunction.of_intertwining`. If moreover `Φ` is a
positive specialization and the normal map keeps primitive normals primitive, then positive
groupings, positive wall representatives, positive representatives of outgoing completions and
completed classes with positive representatives are carried along
(`FunctionWallGrouping.IsPositive.pushforward`,
`DirectedDiagram.IsPositiveWallRepresentative.pushforward`,
`DirectedDiagram.IsOutgoingCompletion.isPositiveWallRepresentative_pushforward`,
`DirectedDiagram.Class.HasPositiveWallRepresentative.pushforward` and
`DirectedDiagram.Class.HasPositiveWallRepresentative.scat_pushforward`). This is the
degree-changing counterpart of
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Specialization`.

For tropical vertex walls pushed along a tropical pairing on all characters
(`DirectedWall.Pushforward.ofTropicalPairing`), take a surjection `τ : Q → Q'` lifting the
degree map `T`, so that `Q' = T(Q)`, and the monomial map `z^q ↦ z^{τ q}`. When the evaluation
identity holds on `Q` and the normal map keeps primitive normals primitive and preserves their
pairings with `Q`, the hypotheses above hold, with the
intertwining `TropicalPairing.mapCompletionₐ_completedBCHAction_tropicalVertexGradedLieHom`
(`DirectedDiagram.IsPositiveWallRepresentative.pushforward_ofTropicalPairing`). In particular this
applies to a positive degree map `T` over a common tangent lattice with `ρ' ∘ T = ρ` on `Q`, such
as an enlargement of the positive monoid
(`DirectedDiagram.IsPositiveWallRepresentative.pushforward_ofTropicalDegreeMap`). For the images
`ι(B)[Q]` and `ι(B)[Q']` of a coefficient semiring the hypothesis on the positive subsemirings is
automatic (`DirectedDiagram.IsPositiveWallRepresentative.pushforward_ofTropicalPairing_rangeS`,
`DirectedDiagram.IsPositiveWallRepresentative.pushforward_ofTropicalDegreeMap_rangeS`), by
`AddMonoidAlgebra.mapDomainAlgHom_mem_rangeS_mapRingHom`. Here the wall
function of a pushed group is the image `Φ(u)` of a source wall function: the hypotheses
require the normal pairings to be preserved exactly. Normal maps scaling the pairings by
`r > 1`, with target wall functions `Φ(u)^r`, are not covered. Transport of positivity along
coefficient maps follows Burcroff–Lee–Mou, §8.1 and §9.2, for the grouped wall functions of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei

universe u v

section Pushforward

variable {Γ Γ' Λ Λ' R V V' M : Type*} {L L' : Type v} {ι : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup M]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [DecidableEq Γ] [DecidableEq Γ']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (P : DirectedWall.Pushforward d d' h h' H H')
  {π : Γ →+ M} {π' : Γ' →+ M} (hπ : ∀ n ∈ d.monoid, π' (P.degreeMap n) = π n)

include hπ in
/-- If `π' ∘ T = π` on allowed degrees, a positive multiple of the projected generator of a wall
is a positive multiple of the projected generator of the pushed wall. -/
theorem DirectedWall.exists_nsmul_projection_pushforward_ray_generator
    (W : DirectedWall (d := d) h H) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      a • π W.ray.generator = b • π' (W.pushforward P).ray.generator := by
  obtain ⟨m, hm⟩ := W.ray.rayDegrees_nonempty
  obtain ⟨hn, a, ha, rfl⟩ := SupportedRay.mem_rayDegrees.mp hm
  obtain ⟨-, b, hb, hbn⟩ := SupportedRay.mem_rayDegrees.mp
    (W.degreeMap_mem_pushforward_rayDegrees P hm)
  refine ⟨a.toNat, b.toNat, by omega, by omega, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ a.toNat, ← Nat.cast_smul_eq_nsmul ℤ b.toNat,
    Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hb.le, ← map_zsmul, ← map_zsmul, ← hbn, hπ _ hn]

namespace DirectedDiagram.FunctionWallGrouping

variable {P} {D : DirectedDiagram (d := d) h H ι} {κ : Type*} (G : D.FunctionWallGrouping π κ)
  (hprim : ∀ j, TauCeti.IsPrimitive (P.normalMap (D.wall j).normal))

/-- If `π' ∘ T = π` on allowed degrees and the normal map keeps the normals of the walls
primitive, a function-wall grouping of a diagram is a grouping of its pushforward, with the same
groups. -/
def pushforward : (D.pushforward P).FunctionWallGrouping π' κ where
  group := G.group
  support_eq hj := by
    rw [pushforward_wall_support, pushforward_wall_support, G.support_eq hj]
  normal_eq hj := by
    rw [pushforward_wall, pushforward_wall, DirectedWall.pushforward_normal,
      DirectedWall.pushforward_normal, G.normal_eq hj]
  projectedDirection_eq {j j'} hj hj1 hj'1 := by
    have hne (j : ι) (h1 : ((D.pushforward P).wall j).label ≠ 1) : (D.wall j).label ≠ 1 :=
      fun he => h1 (by rw [pushforward_wall, DirectedWall.pushforward_label, he, map_one])
    obtain ⟨x, y, hx, hy, hxy⟩ := G.projectedDirection_eq hj (hne j hj1) (hne j' hj'1)
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (D.wall j).exists_nsmul_projection_pushforward_ray_generator P hπ
    obtain ⟨a', b', ha', hb', hab'⟩ :=
      (D.wall j').exists_nsmul_projection_pushforward_ray_generator P hπ
    refine ⟨x * a' * b, y * a * b', by positivity, by positivity, ?_⟩
    rw [pushforward_wall, pushforward_wall]
    calc (x * a' * b) • π' ((D.wall j).pushforward P).ray.generator
        = (x * a') • a • π (D.wall j).ray.generator := by rw [mul_smul, ← hab]
      _ = (a' * a) • x • π (D.wall j).ray.generator := by
        rw [smul_smul, smul_smul]
        congr 1
        ring
      _ = (y * a) • a' • π (D.wall j').ray.generator := by
        rw [hxy, smul_smul, smul_smul]
        congr 1
        ring
      _ = (y * a * b') • π' ((D.wall j').pushforward P).ray.generator := by rw [hab', smul_smul]
  isPrimitive_normal j := by
    simpa only [pushforward_wall, DirectedWall.pushforward_normal] using hprim j

/-- The pushed grouping places every wall in its original group. -/
@[simp]
theorem pushforward_group (j : ι) : (G.pushforward hπ hprim).group j = G.group j := by
  simp [pushforward]

/-- The order-`k` label of a pushed group is the truncated image of the group label at the
order of the cutoff modulus. -/
theorem groupLabel_pushforward (g : κ) (k : ℕ) :
    (G.pushforward hπ hprim).groupLabel g k =
      (P.lieHom.truncatedMap k le_rfl).bchGroupMap (G.groupLabel g (P.degreeMap.modulus k)) := by
  classical
  let s := (Set.toFinite (D.active (P.degreeMap.modulus k))).toFinset.filter
    fun j => G.group j = g
  have hs : ∀ j ∈ s, G.group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hact : ∀ j ∈ D.active (P.degreeMap.modulus k), G.group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite _).mem_toFinset.mpr hj, hg⟩
  rw [(G.pushforward hπ hprim).groupLabel_eq_noncommProd g k s
      (fun j hj => by simpa using hs j hj)
      fun j hj hg => hact j (D.active_pushforward_subset P k le_rfl hj) (by simpa using hg),
    G.groupLabel_eq_noncommProd g _ s hs hact]
  exact (Finset.noncommProd_congr rfl (fun j _ => D.projection_pushforward_wall_label P k le_rfl j)
    _).trans (Finset.map_noncommProd s _ _ _).symm

/-- The completed label of a pushed group is the image of the completed group label. -/
@[simp]
theorem label_pushforward (g : κ) :
    (G.pushforward hπ hprim).label g = P.lieHom.completedMap (G.label g) :=
  (((G.pushforward hπ hprim).eq_label_iff g _).mpr fun k => by
    rw [P.lieHom.projection_completedMap k, projection_label, groupLabel_pushforward]).symm

variable {G} in
/-- A crossing germ of the group `g` at the source order `a`, the point `θ` and the direction
`v` is carried to a crossing germ of the pushed group `g` at every target order `k` whose cutoff
modulus is at most `a`, at the point `A θ` and the direction `A v` for the spatial map `A`. -/
theorem IsCrossingGerm.pushforward {g : κ} {k a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    {θ v : V} (hG : G.IsCrossingGerm g a θ v) :
    (G.pushforward hπ hprim).IsCrossingGerm g k (P.spatialMap θ)
      (P.spatialMap.toAffineEquiv.linear v) where
  notMem_singularSupport hθ := by
    have hs : Convex.singularSupport
        (fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support) =
        P.spatialMap '' Convex.singularSupport
          (fun j : (D.pushforward P).active k => (D.wall j).support) := by
      simp only [pushforward_wall_support]
      exact Convex.singularSupport_image _ _
    rw [hs, P.spatialMap.injective.mem_set_image] at hθ
    exact hG.notMem_singularSupport (Convex.singularSupport_comp_subset _
      (Set.inclusion (D.active_pushforward_subset P k ha)) hθ)
  mem_support_iff j := by
    rw [pushforward_wall_support, P.spatialMap.injective.mem_set_image, pushforward_group]
    exact hG.mem_support_iff (Set.inclusion (D.active_pushforward_subset P k ha) j)
  realCharacter_normal_neg j hj := by
    obtain ⟨r, hr, he⟩ := P.exists_realCharacter_normalMap_apply (D.wall j).normal
    rw [pushforward_wall, DirectedWall.pushforward_normal, he]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hr)
      (hG.realCharacter_normal_neg (Set.inclusion (D.active_pushforward_subset P k ha) j)
        (by simpa using hj))

section WallFunction

open _root_.AddMonoidAlgebra

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
  {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  {F : AlgFiltration (AddMonoidAlgebra A Q)} {F' : AlgFiltration (AddMonoidAlgebra A' Q')}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σ' : d'.completedBCHGroup ℳ →* (F'.completion ≃ₐ[R] F'.completion)}
  {τ : Q → Q'} {G hprim}

/-- Let `Φ` be a ring map of completed coefficient algebras that intertwines the actions along
the completed Lie map of `P`, sends each monomial `z^p` to `z^{τ p}` for a surjection
`τ : Q → Q'`, and such that the target action fixes the constants of `A'`. If the normal map of
`P` preserves the pairings `ν(ρ p)` of the normals `ν` of the walls with all `p ∈ Q`, then `Φ`
sends a wall function of a group to a wall function of the same group of the pushed grouping
`G.pushforward hπ hprim`, which uses `π' ∘ T = π` on allowed degrees and the primitivity of the
pushed normals. -/
theorem IsWallFunction.pushforward (Φ : F.completion →+* F'.completion)
    (hτ : Function.Surjective τ)
    (hmono : ∀ p : Q, Φ (F.toCompletion (single p 1)) = F'.toCompletion (single (τ p) 1))
    (hΦ : ∀ g x, Φ (σ g x) = σ' (P.lieHom.completedMap g) (Φ x))
    (hconst : ∀ g (c : A'),
      σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))
    (hν : ∀ j (p : Q), P.normalMap (D.wall j).normal (ρ' (τ p)) = (D.wall j).normal (ρ p))
    {g : κ} {u : F.completionˣ} (hu : G.IsWallFunction σ g u) :
    (G.pushforward hπ hprim).IsWallFunction σ' g (Units.map Φ.toMonoidHom u) :=
  hu.of_intertwining (G.pushforward hπ hprim) g Φ τ hτ hmono
    (fun x => by rw [label_pushforward]; exact hΦ _ x) (hconst _)
    fun j hj => ⟨j, by simpa using hj, fun p => by
      rw [pushforward_wall, DirectedWall.pushforward_normal, hν]⟩

variable {S : Subsemiring (AddMonoidAlgebra A Q)} {S' : Subsemiring (AddMonoidAlgebra A' Q')}

/-- A positive specialization of completed coefficients that sends each monomial `z^p` to
`z^{τ p}` for a surjection `τ : Q → Q'`, intertwines the actions along the completed Lie map of
`P` and whose target action fixes constants carries a positive grouping to a positive grouping
`G.pushforward hπ hprim` of the pushforward, provided the normal map of `P` preserves the
pairings of the normals of the walls with all `p ∈ Q`. -/
theorem IsPositive.pushforward (φ : PositiveSpecialization F F' S S')
    (hτ : Function.Surjective τ) (hφ : ∀ p : Q, φ.toRingHom (single p 1) = single (τ p) 1)
    (hφσ : ∀ g x, φ.completionMap (σ g x) = σ' (P.lieHom.completedMap g) (φ.completionMap x))
    (hconst : ∀ g (c : A'),
      σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))
    (hν : ∀ j (p : Q), P.normalMap (D.wall j).normal (ρ' (τ p)) = (D.wall j).normal (ρ p))
    (hG : G.IsPositive σ S) : (G.pushforward hπ hprim).IsPositive σ' S' :=
  hG.of_isWallFunction_completionMap (G.pushforward hπ hprim) φ fun _ _ hu =>
    hu.pushforward hπ φ.completionMap hτ (fun p => by rw [φ.completionMap_toCompletion, hφ]) hφσ
      hconst hν

end WallFunction

end DirectedDiagram.FunctionWallGrouping

namespace DirectedDiagram

open _root_.AddMonoidAlgebra

variable {P} {A A' : Type*} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
  {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  {F : AlgFiltration (AddMonoidAlgebra A Q)} {F' : AlgFiltration (AddMonoidAlgebra A' Q')}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σ' : d'.completedBCHGroup ℳ →* (F'.completion ≃ₐ[R] F'.completion)}
  {S : Subsemiring (AddMonoidAlgebra A Q)} {S' : Subsemiring (AddMonoidAlgebra A' Q')}
  {τ : Q → Q'} (φ : PositiveSpecialization F F' S S') (hτ : Function.Surjective τ)
  (hφ : ∀ p : Q, φ.toRingHom (single p 1) = single (τ p) 1)
  (hφσ : ∀ g x, φ.completionMap (σ g x) = σ' (P.lieHom.completedMap g) (φ.completionMap x))
  (hconst : ∀ g (c : A'),
    σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))
  (hprim : ∀ m : Λ →+ ℤ, TauCeti.IsPrimitive m → TauCeti.IsPrimitive (P.normalMap m))
  (hν : ∀ (m : Λ →+ ℤ) (p : Q), P.normalMap m (ρ' (τ p)) = m (ρ p))

include hπ hτ hφ hφσ hconst hprim hν

/-- **Positive wall representatives under pushforward.** Let `φ` be a positive specialization
of completed coefficients sending each monomial `z^p` to `z^{τ p}` for a surjection
`τ : Q → Q'`, intertwining the actions along the completed Lie map of `P`, and such that the
target action fixes constants. If `π' ∘ T = π` on allowed degrees and the normal map of `P`
keeps primitive normals primitive and preserves their pairings with all `p ∈ Q`, then the
pushforward of a positive wall representative is a positive wall representative. -/
theorem IsPositiveWallRepresentative.pushforward {D : DirectedDiagram (d := d) h H ι}
    (hD : D.IsPositiveWallRepresentative σ S π) :
    (D.pushforward P).IsPositiveWallRepresentative σ' S' π' := by
  obtain ⟨κ, G, hG⟩ := (D.isPositiveWallRepresentative_iff σ S π).mp hD
  exact (hG.pushforward hπ (hprim := fun j => hprim _ (G.isPrimitive_normal j)) φ hτ hφ hφσ hconst
    fun j p => hν _ p).isPositiveWallRepresentative

/-- Under the hypotheses of `DirectedDiagram.IsPositiveWallRepresentative.pushforward`, the
pushforward of a positive wall representative of an outgoing completion is a positive wall
representative of an outgoing completion of the pushed initial walls. -/
theorem IsOutgoingCompletion.isPositiveWallRepresentative_pushforward {ι₀ η : Type u}
    {D₀ : ι₀ → DirectedWall (d := d) h H} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ η)}
    (hE : IsOutgoingCompletion D₀ E) (hpos : E.IsPositiveWallRepresentative σ S π) :
    IsOutgoingCompletion (fun j => (D₀ j).pushforward P) (E.pushforward P) ∧
      (E.pushforward P).IsPositiveWallRepresentative σ' S' π' :=
  ⟨hE.pushforward, hpos.pushforward hπ φ hτ hφ hφσ hconst hprim hν⟩

/-- Under the hypotheses of `DirectedDiagram.IsPositiveWallRepresentative.pushforward`, the
pushforward of a completed class with a positive wall representative has one. -/
theorem Class.HasPositiveWallRepresentative.pushforward
    {c : Class.{u} (d := d) (h := h) (H := H)} (hc : c.HasPositiveWallRepresentative σ S π) :
    (Class.pushforward P c).HasPositiveWallRepresentative σ' S' π' := by
  obtain ⟨ι, E, rfl, hE⟩ := (Class.hasPositiveWallRepresentative_iff σ S π c).mp hc
  exact (Class.hasPositiveWallRepresentative_iff σ' S' π' _).mpr ⟨ι, E.pushforward P,
    (Class.pushforward_toClass P E).symm, hE.pushforward hπ φ hτ hφ hφσ hconst hprim hν⟩

/-- Under the hypotheses of `DirectedDiagram.IsPositiveWallRepresentative.pushforward`, if the
scattering class of a full-hyperplane input has a positive wall representative, so does the
scattering class of the pushed input. -/
theorem Class.HasPositiveWallRepresentative.scat_pushforward [Module.Free ℤ Γ]
    [Module.Free ℤ Γ'] (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    (hD : (D.Scat hfull).HasPositiveWallRepresentative σ S π) :
    ((D.pushforward P).Scat (D.pushforward_fullHyperplane P hfull)).HasPositiveWallRepresentative
      σ' S' π' := by
  rw [← pushforward_scat]
  exact hD.pushforward hπ φ hτ hφ hφσ hconst hprim hν

end DirectedDiagram

end Pushforward

namespace DirectedDiagram.FunctionWallGrouping

open LogarithmicVectorField

variable {R Γ Λ Γ' Λ' : Type u} {V V' M : Type*} {ι : Type v} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [AddCommGroup Λ'] [Module.Free ℤ Γ']
  [DecidableEq Γ] [DecidableEq Γ'] [AddCommGroup M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {i : Λ →+ V} {i' : Λ' →+ V'} {h : TauCeti.Toric.IsIntegralLattice i}
  {h' : TauCeti.Toric.IsIntegralLattice i'}
  (T : PositiveDegreeMap d e) (t : Λ →+ Λ') (ht : Function.Injective t)
  [t.range.FiniteIndex] (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n))
  (ν : (Λ →+ ℤ) → (Λ' →+ ℤ)) (q : (Λ →+ ℤ) → ℚ) (hq : ∀ m, 0 < q m)
  (hν : ∀ m x, (ν m (t x) : ℚ) = q m * m x)
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) ι}
  {π : Γ →+ M} {π' : Γ' →+ M} {κ : Type*} (G : D.FunctionWallGrouping π κ)

local notation "P" =>
  DirectedWall.Pushforward.ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν

variable {g : κ} {n : Λ →+ ℤ} {n' : Λ' →+ ℤ} (hn' : ∀ x, (n' (t x) : ℚ) = q n * n x) {r : ℕ}
  (hr : q n = r)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ (AddMonoidHom.comp (Int.castAddHom R) n))
local notation "F'" => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ' (AddMonoidHom.comp (Int.castAddHom R) n'))

include hr in
/-- **Transport of a group label under a finite-index pushforward.** Suppose `π' ∘ T = π` on
allowed degrees (`hπ`) and the normal map sends the normals of all walls to primitive normals
(`hprim`), so that the grouping is pushed forward. Let `n'` be an integral normal with
`n' ∘ t = q n • n`, for instance `ν n`. If the group `g` has the function-wall label
`exp(log(f₀) ∂_n)`, where `q n = r` and the tangent monomial map sends `f₀` to `f₁ ^ r`, then the
pushed group `g` has the function-wall label `exp(log(f₁) ∂_{n'})`. -/
theorem label_pushforward_ofFiniteIndex (hπ : ∀ x ∈ d.monoid, π' ((P).degreeMap x) = π x)
    (hprim : ∀ j, TauCeti.IsPrimitive ((P).normalMap (D.wall j).normal))
    (f₀ : {u : (F).completion // u - 1 ∈ (F).completionIdeal 1})
    (f₁ : {u : (F').completion // u - 1 ∈ (F').completionIdeal 1})
    (hg : G.label g = d.completedBCHExp _ (completedTropicalTangentField d ρ
      ((Int.castAddHom R).comp n) ((F).completedLog f₀)))
    (hf : completedTropicalTangentMap T (map_tropicalTangentMonoid_intCast_le T hρ hn') f₀ =
      (f₁ : (F').completion) ^ r) :
    (G.pushforward hπ hprim).label g = e.completedBCHExp _ (completedTropicalTangentField e ρ'
      ((Int.castAddHom R).comp n') ((F').completedLog f₁)) := by
  rw [label_pushforward, hg]
  exact DirectedWall.Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog
    T t ht hρ ν q hq hν n hn' hr f₀ f₁ hf

include hr in
/-- **Transport of a group label to matched groups of equivalent diagrams.** Under the
hypotheses of `FunctionWallGrouping.label_pushforward_ofFiniteIndex`, let `E` be any diagram
equivalent to the finite-index pushforward of `D`, with a function-wall grouping `G'`. Suppose
that at every order `k` there is a crossing germ of `g` at the source order `T.modulus k`, at a
point `θ` and a direction `v`, and a crossing germ of the group `g'` of `G'` at order `k`, at the
images `A θ` and `A v` under the spatial map `A`. Then `g'` has the function-wall label
`exp(log(f₁) ∂_{n'})`, the label of an `r`-th root `f₁` of `T_* f₀`. The crossing germs are
hypotheses. -/
theorem label_eq_of_equivalent_pushforward_ofFiniteIndex
    (hπ : ∀ x ∈ d.monoid, π' ((P).degreeMap x) = π x)
    (hprim : ∀ j, TauCeti.IsPrimitive ((P).normalMap (D.wall j).normal))
    (f₀ : {u : (F).completion // u - 1 ∈ (F).completionIdeal 1})
    (f₁ : {u : (F').completion // u - 1 ∈ (F').completionIdeal 1})
    (hg : G.label g = d.completedBCHExp _ (completedTropicalTangentField d ρ
      ((Int.castAddHom R).comp n) ((F).completedLog f₀)))
    (hf : completedTropicalTangentMap T (map_tropicalTangentMonoid_intCast_le T hρ hn') f₀ =
      (f₁ : (F').completion) ^ r)
    {ι' κ' M' : Type*} [AddCommGroup M'] {π'' : Γ' →+ M'}
    {E : DirectedDiagram (d := e) h' (tropicalVertexWallSpaces (R := R) e ρ') ι'}
    (hDE : (D.pushforward (P)).Equivalent E) (G' : E.FunctionWallGrouping π'' κ') {g' : κ'}
    (hgerm : ∀ k, ∃ θ v, G.IsCrossingGerm g (T.modulus k) θ v ∧
      G'.IsCrossingGerm g' k ((P).spatialMap θ) ((P).spatialMap.toAffineEquiv.linear v)) :
    G'.label g' = e.completedBCHExp _ (completedTropicalTangentField e ρ'
      ((Int.castAddHom R).comp n') ((F').completedLog f₁)) :=
  (label_eq_of_equivalent hDE fun k => by
    obtain ⟨θ, v, hθ, hθ'⟩ := hgerm k
    exact ⟨_, _, hθ.pushforward hπ hprim (by simp), hθ'⟩).symm.trans
      (G.label_pushforward_ofFiniteIndex T t ht hρ ν q hq hν hn' hr hπ hprim f₀ f₁ hg hf)

end DirectedDiagram.FunctionWallGrouping

namespace DirectedDiagram

open LogarithmicVectorField _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

section OfTropicalPairing

variable {R Γ Λ Γ' Λ' : Type u} {V V' M : Type*} {ι : Type v} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [AddCommGroup Λ'] [Module.Free ℤ Γ']
  [DecidableEq Γ] [DecidableEq Γ'] [AddCommGroup M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {i : Λ →+ V} {i' : Λ' →+ V'} {h : TauCeti.Toric.IsIntegralLattice i}
  {h' : TauCeti.Toric.IsIntegralLattice i'}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') (⊤ : Submodule R (Λ →+ R)))
  (ν : (Λ →+ ℤ) → (Λ' →+ ℤ))
  (hν : ∀ m, p.characterMap ⟨(Int.castAddHom R).comp m, Submodule.mem_top⟩ ∈
    R ∙ (Int.castAddHom R).comp (ν m))
  (A : V ≃ᴬ[ℝ] V')
  (hA : ∀ n ∈ d.monoid, i' (ρ' (p.degreeMap n)) = A.toAffineEquiv.linear (i (ρ n)))
  (hνA : ∀ m, ∃ r : ℚ, 0 < r ∧
    (h'.realCharacter (ν m)).comp A.toAffineEquiv.linear.toLinearMap =
      (r : ℝ) • h.realCharacter m)
  {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'} [Fact (d.monoid ≤ Q)] [Fact (e.monoid ≤ Q')]
  (τ : Q →+ Q') (hτ : ∀ q : Q, (τ q : Γ') = p.degreeMap q) (hτs : Function.Surjective τ)
  {π : Γ →+ M} {π' : Γ' →+ M} (hπ : ∀ n ∈ d.monoid, π' (p.degreeMap n) = π n)
  (heval : ∀ (m : (⊤ : Submodule R (Λ →+ R))) {q : Γ}, q ∈ Q →
    p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
  (hprim : ∀ m : Λ →+ ℤ, TauCeti.IsPrimitive m → TauCeti.IsPrimitive (ν m))
  (hνQ : ∀ (m : Λ →+ ℤ) {q : Γ}, q ∈ Q → ν m (ρ' (p.degreeMap q)) = m (ρ q))
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) ι}

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "F'" => TropicalVertexCoefficientAction.filtration (R := R) e Q'

include hτ hτs hπ heval hprim hνQ

/-- **Positive wall representatives along tropical pairings.** Let `p` be a tropical pairing
on all characters, pushing tropical vertex walls forward by `ofTropicalPairing p ν hν A hA hνA`,
and let `τ : Q → Q'` be a surjection of coefficient monoids lifting the degree map `T`, so that
`Q' = T(Q)`. Assume that the evaluation identity of `p` holds on `Q`, that `ν` keeps primitive
normals primitive and preserves the pairings of integral normals with `Q`, that `π' ∘ T = π` on
allowed degrees, and that the monomial map `z^q ↦ z^{τ q}` sends the positive subsemiring `S`
into `S'`. Then the pushforward of a positive wall representative for the tropical vertex action
on `R[[Q]]` is a positive wall representative for the tropical vertex action on `R[[Q']]`. -/
theorem IsPositiveWallRepresentative.pushforward_ofTropicalPairing
    {S : Subsemiring R[Q]} {S' : Subsemiring R[Q']} (hS : ∀ a ∈ S, mapDomainAlgHom R R τ a ∈ S')
    (hD : D.IsPositiveWallRepresentative
      ((F).completedBCHAction d (tropicalVertexGrading (R := R) d ρ)) S π) :
    (D.pushforward (DirectedWall.Pushforward.ofTropicalPairing p ν hν A hA hνA)
      ).IsPositiveWallRepresentative
        ((F').completedBCHAction e (tropicalVertexGrading (R := R) e ρ')) S' π' := by
  have hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q' := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← hτ ⟨q, hq⟩]
    exact (τ ⟨q, hq⟩).property
  let θ : Q →+ Q' := (AddSubmonoid.inclusion hT).comp (p.degreeMap.toAddMonoidHom.addSubmonoidMap Q)
  obtain rfl : τ = θ := AddMonoidHom.ext fun q => Subtype.ext (by rw [hτ]; simp [θ])
  have hψ := TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom
    (R := R) p.degreeMap hT
  let φ : PositiveSpecialization F F' S S' :=
    { toRingHom := mapDomainAlgHom R R θ
      exists_modulus := ⟨p.degreeMap.modulus, p.degreeMap.monotone_modulus, hψ⟩
      map_mem := hS }
  have hφ (x : (F).completion) : φ.completionMap x =
      (F).mapCompletionₐ F' (mapDomainAlgHom R R θ) p.degreeMap.modulus
        p.degreeMap.monotone_modulus hψ x := by
    rw [φ.completionMap_eq_mapCompletion p.degreeMap.modulus p.degreeMap.monotone_modulus hψ,
      ← AlgFiltration.coe_mapCompletionₐ, AlgHom.coe_toRingHom]
  have hlie : (DirectedWall.Pushforward.ofTropicalPairing (h := h) (h' := h') p ν hν A hA hνA
      ).lieHom.completedMap = p.tropicalVertexGradedLieHom.completedMap :=
    GradedLieHom.completedMap_eq_of_toLieHom_eq _ _ (LieHom.ext fun x =>
      DirectedWall.Pushforward.ofTropicalPairing_lieHom_apply p ν hν A hA hνA x)
  refine hD.pushforward (by simpa only [DirectedWall.Pushforward.ofTropicalPairing_degreeMap])
    φ hτs (fun q => ?_) (fun g x => ?_)
    (fun g c => AlgFiltration.algEquiv_toCompletion_single_zero _ c)
    (fun m hm => by
      rw [DirectedWall.Pushforward.ofTropicalPairing_normalMap]
      exact hprim m hm)
    (fun m q => by
      rw [DirectedWall.Pushforward.ofTropicalPairing_normalMap, hτ]
      exact hνQ m q.property)
  · simp only [φ, RingHom.coe_coe, mapDomainAlgHom_apply, mapDomain_single]
  · rw [hφ, hφ, hlie]
    exact p.mapCompletionₐ_completedBCHAction_tropicalVertexGradedLieHom hT heval g x

/-- `DirectedDiagram.IsPositiveWallRepresentative.pushforward_ofTropicalPairing` for the images
`ι(B)[Q]` and `ι(B)[Q']` of a coefficient semiring `B`, such as `ℕ[c] ⊆ ℚ[c]`: the monomial map
sends one into the other (`AddMonoidAlgebra.mapDomainAlgHom_mem_rangeS_mapRingHom`). -/
theorem IsPositiveWallRepresentative.pushforward_ofTropicalPairing_rangeS {B : Type*}
    [CommSemiring B] (ι : B →+* R)
    (hD : D.IsPositiveWallRepresentative
      ((F).completedBCHAction d (tropicalVertexGrading (R := R) d ρ))
      (AddMonoidAlgebra.mapRingHom Q ι).rangeS π) :
    (D.pushforward (DirectedWall.Pushforward.ofTropicalPairing p ν hν A hA hνA)
      ).IsPositiveWallRepresentative
        ((F').completedBCHAction e (tropicalVertexGrading (R := R) e ρ'))
        (AddMonoidAlgebra.mapRingHom Q' ι).rangeS π' :=
  hD.pushforward_ofTropicalPairing p ν hν A hA hνA τ hτ hτs hπ heval hprim hνQ
    fun _ ha => mapDomainAlgHom_mem_rangeS_mapRingHom ι τ ha

end OfTropicalPairing

section OfTropicalDegreeMap

variable {R Γ Λ Γ' : Type u} {V M : Type*} {ι : Type v} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [Module.Free ℤ Γ']
  [DecidableEq Γ] [DecidableEq Γ'] [AddCommGroup M] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ}
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (T : PositiveDegreeMap d e) (hT : ∀ n ∈ d.monoid, ρ' (T n) = ρ n)
  {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'} [Fact (d.monoid ≤ Q)] [Fact (e.monoid ≤ Q')]
  (τ : Q →+ Q') (hτ : ∀ q : Q, (τ q : Γ') = T q) (hτs : Function.Surjective τ)
  (hρQ : ∀ q ∈ Q, ρ' (T q) = ρ q)
  {π : Γ →+ M} {π' : Γ' →+ M} (hπ : ∀ n ∈ d.monoid, π' (T n) = π n)
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) ι}

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "F'" => TropicalVertexCoefficientAction.filtration (R := R) e Q'

include hτ hτs hρQ hπ

/-- **Positive wall representatives along degree maps over a common tangent lattice.** Let
`T` be a positive degree map with `ρ' ∘ T = ρ` on the coefficient monoid `Q`, and let
`τ : Q → Q'` be a surjection lifting `T`, so that `Q' = T(Q)`. If `π' ∘ T = π` on allowed
degrees and the monomial map `z^q ↦ z^{τ q}` sends the positive subsemiring `S` into `S'`, the
pushforward along `ofTropicalDegreeMap T hT`, which keeps supports and normals, carries positive
wall representatives for the tropical vertex action on `R[[Q]]` to positive wall
representatives for the tropical vertex action on `R[[Q']]`. -/
theorem IsPositiveWallRepresentative.pushforward_ofTropicalDegreeMap
    {S : Subsemiring R[Q]} {S' : Subsemiring R[Q']} (hS : ∀ a ∈ S, mapDomainAlgHom R R τ a ∈ S')
    (hD : D.IsPositiveWallRepresentative
      ((F).completedBCHAction d (tropicalVertexGrading (R := R) d ρ)) S π) :
    (D.pushforward (DirectedWall.Pushforward.ofTropicalDegreeMap T hT)
      ).IsPositiveWallRepresentative
        ((F').completedBCHAction e (tropicalVertexGrading (R := R) e ρ')) S' π' := by
  rw [DirectedWall.Pushforward.ofTropicalDegreeMap_eq_ofTropicalPairing]
  exact hD.pushforward_ofTropicalPairing _ _ _ _ _ _ τ
    (fun q => by rw [TropicalPairing.ofDegreeMap_degreeMap, hτ]) hτs
    (by simpa only [TropicalPairing.ofDegreeMap_degreeMap] using hπ)
    (fun m q hq => by
      rw [TropicalPairing.ofDegreeMap_characterMap, TropicalPairing.ofDegreeMap_degreeMap,
        hρQ q hq])
    (fun _ hm => hm) (fun m q hq => by rw [TropicalPairing.ofDegreeMap_degreeMap, hρQ q hq]) hS

/-- `DirectedDiagram.IsPositiveWallRepresentative.pushforward_ofTropicalDegreeMap` for the
images `ι(B)[Q]` and `ι(B)[Q']` of a coefficient semiring `B`, such as `ℕ[c] ⊆ ℚ[c]`. -/
theorem IsPositiveWallRepresentative.pushforward_ofTropicalDegreeMap_rangeS {B : Type*}
    [CommSemiring B] (ι : B →+* R)
    (hD : D.IsPositiveWallRepresentative
      ((F).completedBCHAction d (tropicalVertexGrading (R := R) d ρ))
      (AddMonoidAlgebra.mapRingHom Q ι).rangeS π) :
    (D.pushforward (DirectedWall.Pushforward.ofTropicalDegreeMap T hT)
      ).IsPositiveWallRepresentative
        ((F').completedBCHAction e (tropicalVertexGrading (R := R) e ρ'))
        (AddMonoidAlgebra.mapRingHom Q' ι).rangeS π' :=
  hD.pushforward_ofTropicalDegreeMap T hT τ hτ hτs hρQ hπ
    fun _ ha => mapDomainAlgHom_mem_rangeS_mapRingHom ι τ ha

end OfTropicalDegreeMap

end DirectedDiagram

end Mei
