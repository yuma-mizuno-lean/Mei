/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Ray.LogSum
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallFamily
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor

/-!
# Ray presentations of labels on affine hyperplanes

Let affine hyperplanes `{μ_j = a_j}` with nonzero integral normals `μ_j` carry completed tropical
vertex labels `g_j` whose ray factors are wall labels with normal `μ_j`, for instance the
function-wall labels `exp(log(f_j) ∂_{μ_j})` of tangent polynomials
(`rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup`). If only finitely
many labels have a ray factor surviving each cutoff, the ray factors of `g_j` on the supported
rays tangent to `μ_j`, placed on the whole hyperplane, form a directed diagram
(`DirectedDiagram.ofHyperplaneRayFactors`). Its walls are incoming full hyperplanes, and the
hyperplanes form families in the sense of `DirectedDiagram.familyLog`: at every order the family
logarithm of `j` is the logarithm of `g_j` (`DirectedDiagram.familyLog_ofHyperplaneRayFactors`).

More generally, a diagram is a *ray presentation* of labels `g_j` on supports `S_j`
(`DirectedDiagram.IsRayFactorPresentation`) when its walls are indexed by pairs `(j, w)` of a
label and a supported ray tangent to `μ_j`, and the wall `(j, w)` lies on `S_j` with normal
`μ_j`, ray `w` and the ray factor of `g_j` on `w` as label. The diagram of labels on affine
hyperplanes is one (`DirectedDiagram.isRayFactorPresentation_ofHyperplaneRayFactors`).

This is the common ray presentation of the incoming diagrams of
`RankTwoPolynomialInput.incomingDiagram`, `BLMPolynomialInput.incomingDiagram` and
`HyperplaneTermInput.diagram`. The splitting of function walls into ray walls follows
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

namespace Mei.DirectedDiagram

variable {R Γ Λ V ι : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [AddCommGroup Λ]
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The diagram `D` is a ray presentation of the labels `g_j` on the supports `S_j`: the wall
`(j, w)`, for a supported ray `w` tangent to `μ_j`, has support `S_j`, normal `μ_j`, ray `w`
and the ray factor of `g_j` on `w` as label. -/
structure IsRayFactorPresentation {μ : ι → Λ →+ ℤ}
    (D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
      (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}))
    (S : ι → Set V) (g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)) :
    Prop where
  /-- The wall `(j, w)` lies on `S_j`. -/
  support (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    (D.wall x).support = S x.1
  /-- The wall `(j, w)` is cooriented by `μ_j`. -/
  normal (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) : (D.wall x).normal = μ x.1
  /-- The wall `(j, w)` lies on the ray `w`. -/
  ray (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) : (D.wall x).ray = x.2.val
  /-- The wall `(j, w)` carries the ray factor of `g_j` on `w`. -/
  label (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    (D.wall x).label = d.rayFactor (tropicalVertexGrading (R := R) d ρ) (g x.1) x.2.val

variable (h) (μ : ι → Λ →+ ℤ) (hμ : ∀ j, μ j ≠ 0) (a : ι → ℝ)
  (g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ))
  (hg : ∀ j w, d.rayFactor _ (g j) w ∈ (tropicalVertexWallSpaces d ρ).wallGroup w (μ j))
  (hfin : TauCeti.CompletedGroup.HasFiniteSupport
    fun x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0} =>
      d.rayFactor (tropicalVertexGrading (R := R) d ρ) (g x.1) x.2.val)

/-- The ray presentation of labels `g_j` on the affine hyperplanes `{μ_j = a_j}`: the ray factor
of `g_j` on each supported ray tangent to `μ_j`, on the whole hyperplane. -/
def ofHyperplaneRayFactors : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) where
  wall x := DirectedWall.ofAffineHyperplane h _ (μ x.1) (hμ x.1) (a x.1) x.2.val x.2.property
    ⟨d.rayFactor _ (g x.1) x.2.val, hg x.1 x.2.val⟩
  finite_active := by simpa only [DirectedWall.ofAffineHyperplane_label] using hfin

variable (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})

/-- The wall over the hyperplane `j` is cooriented by `μ_j`. -/
@[simp]
theorem ofHyperplaneRayFactors_normal :
    ((ofHyperplaneRayFactors h μ hμ a g hg hfin).wall x).normal = μ x.1 := by
  simp [ofHyperplaneRayFactors]

/-- The wall indexed by a tangent supported ray lies on that ray. -/
@[simp]
theorem ofHyperplaneRayFactors_ray :
    ((ofHyperplaneRayFactors h μ hμ a g hg hfin).wall x).ray = x.2.val := by
  simp [ofHyperplaneRayFactors]

/-- The wall over the hyperplane `j` is supported on the whole hyperplane `{μ_j = a_j}`. -/
@[simp]
theorem ofHyperplaneRayFactors_support :
    ((ofHyperplaneRayFactors h μ hμ a g hg hfin).wall x).support =
      {y | h.realCharacter (μ x.1) y = a x.1} := by
  simp [ofHyperplaneRayFactors]

/-- The wall over the hyperplane `j` on the ray `w` carries the ray factor of `g_j` on `w`. -/
@[simp]
theorem ofHyperplaneRayFactors_label :
    ((ofHyperplaneRayFactors h μ hμ a g hg hfin).wall x).label = d.rayFactor _ (g x.1) x.2.val :=
  by simp [ofHyperplaneRayFactors]

/-- Every wall is incoming. -/
@[simp]
theorem ofHyperplaneRayFactors_incoming :
    ((ofHyperplaneRayFactors h μ hμ a g hg hfin).wall x).Incoming := by
  simp [ofHyperplaneRayFactors]

/-- The ray factors of labels on affine hyperplanes form a ray presentation on the
hyperplanes. -/
theorem isRayFactorPresentation_ofHyperplaneRayFactors :
    (ofHyperplaneRayFactors h μ hμ a g hg hfin).IsRayFactorPresentation
      (fun j => {y | h.realCharacter (μ j) y = a j}) g where
  support := ofHyperplaneRayFactors_support h μ hμ a g hg hfin
  normal := ofHyperplaneRayFactors_normal h μ hμ a g hg hfin
  ray := ofHyperplaneRayFactors_ray h μ hμ a g hg hfin
  label := ofHyperplaneRayFactors_label h μ hμ a g hg hfin

/-- Every wall is a full affine hyperplane, as required for outgoing completion. -/
theorem ofHyperplaneRayFactors_full : ∃ b : ℝ,
    ((ofHyperplaneRayFactors h μ hμ a g hg hfin).wall x).support =
      {y | h.realCharacter ((ofHyperplaneRayFactors h μ hμ a g hg hfin).wall x).normal y = b} :=
  ⟨a x.1, by rw [ofHyperplaneRayFactors_support, ofHyperplaneRayFactors_normal]⟩

/-- At every order, the walls over the hyperplane `j` have the logarithm of `g_j` as their family
logarithm. -/
theorem familyLog_ofHyperplaneRayFactors [Module.Free ℤ Γ] (k : ℕ) (j : ι) :
    (ofHyperplaneRayFactors h μ hμ a g hg hfin).familyLog Sigma.fst k j =
      BCHGroup.log (L := d.lieTruncation (tropicalVertexGrading (R := R) d ρ) k)
        (TauCeti.CompletedGroup.projection k (g j)) := by
  classical
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ _
  let A := (d.finite_raysAtOrder k).toFinset
  let s : Finset (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :=
    (A.subtype fun w => μ j (ρ w.generator) = 0).map (Function.Embedding.sigmaMk j)
  have hs (x) (hx : x ∈ s) : x.1 = j := by
    obtain ⟨⟨w, hw⟩, -, rfl⟩ := Finset.mem_map.mp hx
    simp
  have hact (x) (hx : x ∈ (ofHyperplaneRayFactors h μ hμ a g hg hfin).active k)
      (hxj : x.1 = j) : x ∈ s := by
    obtain ⟨j', w, hw⟩ := x
    obtain rfl : j' = j := hxj
    refine Finset.mem_map.mpr ⟨⟨w, hw⟩, Finset.mem_subtype.mpr ?_, rfl⟩
    refine (d.finite_raysAtOrder k).mem_toFinset.mpr (not_not.mp fun hwk => ?_)
    refine (ofHyperplaneRayFactors h μ hμ a g hg hfin).mem_active k _ |>.mp hx ?_
    rw [ofHyperplaneRayFactors_label]
    exact d.projection_eq_one_of_notMem_raysAtOrder _
      (d.rayFactor_mem_completedRaySubgroup _ _ _) k hwk
  rw [familyLog_eq_sum _ Sigma.fst k j s hs hact, Finset.sum_map,
    d.log_projection_eq_sum_log_projection_rayFactor _ _ k A (by simp [A])]
  simp only [Function.Embedding.sigmaMk_apply, ofHyperplaneRayFactors_label]
  rw [Finset.sum_subtype_eq_sum_filter (fun w => BCHGroup.log
      (L := d.lieTruncation (tropicalVertexGrading (R := R) d ρ) k)
      (TauCeti.CompletedGroup.projection k (d.rayFactor _ (g j) w))),
    Finset.sum_filter_of_ne fun w _ hw => ?_]
  by_contra hn
  have h1 := hg j w
  rw [(tropicalVertexWallSpaces d ρ).wallGroup_eq_bot_of_normal_ne_zero hn,
    Subgroup.mem_bot] at h1
  rw [h1] at hw
  exact hw (by rw [map_one]; exact BCHGroup.log_one)

end Mei.DirectedDiagram
