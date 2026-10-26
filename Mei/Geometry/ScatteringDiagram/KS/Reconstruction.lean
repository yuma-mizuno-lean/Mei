/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Map
public import Mei.Geometry.ScatteringDiagram.KS.Sign
public import Mei.Algebra.Lie.BCH.Sign.Map

/-!
# Middle-factor labels on finite KS arrangements

Every element of a truncated BCH group determines a KS complex on its bounded-degree
hyperplane arrangement. Each wall is cooriented by a retained positive degree and
labelled by the middle sign factor at any relative interior point. The three sign
factors are well defined on all arrangement cells, locally constant off the walls,
and their product recovers the original group element. The middle factor belongs to
the orthogonal subgroup of the whole cell. Cutoff projection preserves these labels
wherever the two wall interiors meet. Degree-preserving coefficient maps commute with
finite reconstruction as an equality of KS complexes: the same arrangement and
coorientations carry the images of the original middle-factor labels.

This constructs the finite labelled complexes; it does not assert their consistency
or compatibility on paths. The construction follows Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416), §§3.2 and 3.4, using
`PositiveDegrees.signFactorizationEquiv`, the relative-interior sign identities in
`Mei.Geometry.ScatteringDiagram.KS.Sign`, and the existing `KSComplex` carrier.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open Set Filter Topology Mei.Convex

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {k l : ℕ}

/-- All three multiplicative sign factors are constant on each arrangement
cell's relative interior. -/
theorem signFactor_eq_of_mem_intrinsicInterior_arrangementComplex
    {P : Set (V →L[ℝ] ℝ)} (hP : P ∈ (d.arrangementComplex h k).cells)
    {θ φ : V →L[ℝ] ℝ} (hθ : θ ∈ intrinsicInterior ℝ P)
    (hφ : φ ∈ intrinsicInterior ℝ P) (g : d.truncatedGroup ℒ k) (s : SignType) :
    ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g s :
        d.truncatedGroup ℒ k) =
      ((signFactorizationEquiv ℒ (φ.toAddMonoidHom.comp i) d k).symm g s :
        d.truncatedGroup ℒ k) :=
  signFactorizationEquiv_symm_eq_of_signSubalgebra_eq ℒ _ d _ k
    (d.signSubalgebra_eq_of_mem_intrinsicInterior_arrangementComplex h ℒ hP hθ hφ) g s

/-- Off the walls of the arrangement, all three sign factors are locally constant. -/
theorem eventually_signFactor_eq_of_notMem_arrangementComplex_walls {θ : V →L[ℝ] ℝ}
    (hθ : ∀ P : (d.arrangementComplex h k).walls, θ ∉ (P : Set (V →L[ℝ] ℝ)))
    (g : d.truncatedGroup ℒ k) (s : SignType) :
    ∀ᶠ φ in 𝓝 θ, ((signFactorizationEquiv ℒ (φ.toAddMonoidHom.comp i) d k).symm g s :
        d.truncatedGroup ℒ k) =
      ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g s :
        d.truncatedGroup ℒ k) := by
  have hrow (n : ↥(d.cutoff k \ {0})) :
      ∀ᶠ φ in 𝓝 θ, SignType.sign (φ (i n)) = SignType.sign (θ (i n)) := by
    have hz : θ (i n) ≠ 0 := fun hz => by
      obtain ⟨P, hP, hθP⟩ := d.exists_mem_arrangementComplex_walls_of_eval_eq_zero h n.property hz
      exact hθ ⟨P, hP⟩ hθP
    have hsign := ((continuousAt_sign_of_ne_zero hz).comp
      (f := fun φ : V →L[ℝ] ℝ => φ (i n))
      (ContinuousLinearMap.apply ℝ ℝ (i n)).continuous.continuousAt).tendsto
    simpa only [nhds_discrete, tendsto_pure, Function.comp_def] using hsign
  filter_upwards [eventually_all.mpr hrow] with φ hφ
  refine signFactorizationEquiv_symm_eq_of_signSubalgebra_eq ℒ _ d _ k
    (fun s' => signSubalgebra_eq_of_sign_eq _ _ _ (fun n hn => ?_) s') g s
  simpa using hφ ⟨n, d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hn⟩

private def arrangementCellPoint (P : (d.arrangementComplex h k).cells) :
    intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ)) := by
  let := h.continuousDual.finiteDimensional
  have hne := (intrinsicInterior_nonempty
    ((d.arrangementComplex h k).isConvexPolyhedron P.property).convex).mpr
    ((d.arrangementComplex h k).nonempty P P.property)
  exact ⟨hne.choose, hne.choose_spec⟩

/-- The positive, middle or negative sign factor of a group element on an
arrangement cell, independent of the relative interior point used to extract it. -/
def arrangementSignFactor (g : d.truncatedGroup ℒ k)
    (P : (d.arrangementComplex h k).cells) (s : SignType) : d.truncatedGroup ℒ k :=
  ((signFactorizationEquiv ℒ
    ((d.arrangementCellPoint h P).val.toAddMonoidHom.comp i) d k).symm g s :
      d.truncatedGroup ℒ k)

/-- Any relative interior point computes the cell's sign factors. -/
theorem arrangementSignFactor_eq (g : d.truncatedGroup ℒ k)
    (P : (d.arrangementComplex h k).cells) {θ : V →L[ℝ] ℝ}
    (hθ : θ ∈ intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ))) (s : SignType) :
    d.arrangementSignFactor h ℒ g P s =
      ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g s :
        d.truncatedGroup ℒ k) :=
  d.signFactor_eq_of_mem_intrinsicInterior_arrangementComplex h ℒ P.property
    (d.arrangementCellPoint h P).property hθ g s

/-- The factor has the prescribed sign at every relative interior point. -/
theorem arrangementSignFactor_mem (g : d.truncatedGroup ℒ k)
    (P : (d.arrangementComplex h k).cells) {θ : V →L[ℝ] ℝ}
    (hθ : θ ∈ intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ))) (s : SignType) :
    d.arrangementSignFactor h ℒ g P s ∈
      (signSubalgebra (d.truncatedGrading ℒ k) (θ.toAddMonoidHom.comp i) s).bchSubgroup := by
  rw [d.arrangementSignFactor_eq h ℒ g P hθ s]
  exact ((signFactorizationEquiv ℒ _ d k).symm g s).property

/-- The three cell factors recombine to the original group element. -/
theorem arrangementSignFactor_mul (g : d.truncatedGroup ℒ k)
    (P : (d.arrangementComplex h k).cells) :
    d.arrangementSignFactor h ℒ g P .pos * d.arrangementSignFactor h ℒ g P .zero *
      d.arrangementSignFactor h ℒ g P .neg = g := by
  obtain ⟨θ, hθ⟩ := d.arrangementCellPoint h P
  simp only [d.arrangementSignFactor_eq h ℒ g P hθ]
  simpa only [signFactorizationEquiv_apply] using
    (signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).apply_symm_apply g

/-- Identity group elements have identity factors on every cell. -/
@[simp]
theorem arrangementSignFactor_one (P : (d.arrangementComplex h k).cells) (s : SignType) :
    d.arrangementSignFactor h ℒ 1 P s = 1 := by
  obtain ⟨θ, hθ⟩ := d.arrangementCellPoint h P
  rw [d.arrangementSignFactor_eq h ℒ 1 P hθ s, signFactorizationEquiv_symm_one]
  rfl

/-- The middle factor is an admissible orthogonal label for the whole closed cell. -/
theorem arrangementSignFactor_zero_mem_orthogonal (g : d.truncatedGroup ℒ k)
    (P : (d.arrangementComplex h k).cells) :
    d.arrangementSignFactor h ℒ g P 0 ∈
      (orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
        ((KSSpace.continuousDual h).evaluation '' (P : Set (V →L[ℝ] ℝ)))).bchSubgroup := by
  obtain ⟨θ, hθ⟩ := d.arrangementCellPoint h P
  have he : ((KSSpace.continuousDual h).evaluation : _ → _) =
      fun φ : V →L[ℝ] ℝ => φ.toAddMonoidHom.comp i := by
    ext φ n
    simp
  rw [he, ← d.signSubalgebra_zero_eq_orthogonalLieSubalgebra h ℒ P.property hθ]
  exact d.arrangementSignFactor_mem h ℒ g P hθ 0

/-- If two cells at different cutoffs have a common relative interior point,
projection preserves all three factors. -/
theorem truncationMap_arrangementSignFactor (hkl : k ≤ l)
    (g : d.truncatedGroup ℒ l)
    (P : (d.arrangementComplex h k).cells) (Q : (d.arrangementComplex h l).cells)
    {θ : V →L[ℝ] ℝ} (hθP : θ ∈ intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ)))
    (hθQ : θ ∈ intrinsicInterior ℝ (Q : Set _)) (s : SignType) :
    (d.truncationMap ℒ hkl).bchGroupMap (d.arrangementSignFactor h ℒ g Q s) =
      d.arrangementSignFactor h ℒ ((d.truncationMap ℒ hkl).bchGroupMap g) P s := by
  rw [d.arrangementSignFactor_eq h ℒ g Q hθQ s,
    d.arrangementSignFactor_eq h ℒ _ P hθP s]
  exact truncationMap_signFactorizationEquiv_symm ℒ _ d hkl g s

omit [DecidableEq N] in
private def arrangementWallDegree (P : (d.arrangementComplex h k).walls) : N :=
  (d.exists_degree_forall_eq_zero_of_mem_arrangementComplex_walls h P.property).choose

omit [DecidableEq N] in
private theorem arrangementWallDegree_spec (P : (d.arrangementComplex h k).walls) :
    d.arrangementWallDegree h P ∈ d.cutoff k \ {0} ∧
      ∀ θ ∈ (P : Set (V →L[ℝ] ℝ)), θ (i (d.arrangementWallDegree h P)) = 0 :=
  (d.exists_degree_forall_eq_zero_of_mem_arrangementComplex_walls h P.property).choose_spec

/-- The finite middle-factor KS complex of a truncated group element.
This assigns actual wall data; consistency is a separate assertion. -/
def reconstructFinite (g : d.truncatedGroup ℒ k) :
    KSComplex (KSSpace.continuousDual h) d ℒ (d.arrangementComplex h k) k where
  isConical := d.isConical_arrangementComplex h k
  degree := d.arrangementWallDegree h
  degree_mem P := (d.mem_cutoff.mp (d.arrangementWallDegree_spec h P).1.1).1
  degree_ne_zero P := (d.arrangementWallDegree_spec h P).1.2
  evaluation_eq_zero P θ hθ := by
    simpa using (d.arrangementWallDegree_spec h P).2 θ hθ
  label P := d.arrangementSignFactor h ℒ g
    ⟨P, (d.arrangementComplex h k).mem_cells_of_mem_walls P.property⟩ 0
  label_mem P := d.arrangementSignFactor_zero_mem_orthogonal h ℒ g
    ⟨P, (d.arrangementComplex h k).mem_cells_of_mem_walls P.property⟩

/-- The chosen coorienting degree is nonzero and survives the cutoff. -/
theorem reconstructFinite_degree_mem_cutoff (g : d.truncatedGroup ℒ k)
    (P : (d.arrangementComplex h k).walls) :
    (d.reconstructFinite h ℒ g).degree P ∈ d.cutoff k \ {0} :=
  (d.arrangementWallDegree_spec h P).1

/-- Reconstruction uses the same geometric coorientations for every group element. -/
theorem reconstructFinite_degree_eq (g g' : d.truncatedGroup ℒ k) :
    (d.reconstructFinite h ℒ g).degree = (d.reconstructFinite h ℒ g').degree := (rfl)

/-- The wall label is the middle factor at any of its relative interior points. -/
theorem reconstructFinite_label (g : d.truncatedGroup ℒ k)
    (P : (d.arrangementComplex h k).walls) {θ : V →L[ℝ] ℝ}
    (hθ : θ ∈ intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ))) :
    (d.reconstructFinite h ℒ g).label P =
      ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g 0 :
        d.truncatedGroup ℒ k) :=
  d.arrangementSignFactor_eq h ℒ g
    ⟨P, (d.arrangementComplex h k).mem_cells_of_mem_walls P.property⟩ hθ 0

/-- The identity reconstructs with identity labels on all walls. -/
@[simp]
theorem reconstructFinite_one_label (P : (d.arrangementComplex h k).walls) :
    (d.reconstructFinite h ℒ 1).label P = 1 := by
  exact d.arrangementSignFactor_one h ℒ
    ⟨P, (d.arrangementComplex h k).mem_cells_of_mem_walls P.property⟩ 0

/-- Projection preserves reconstructed wall labels on overlapping relative interiors. -/
theorem truncationMap_reconstructFinite_label (hkl : k ≤ l)
    (g : d.truncatedGroup ℒ l)
    (P : (d.arrangementComplex h k).walls) (Q : (d.arrangementComplex h l).walls)
    {θ : V →L[ℝ] ℝ} (hθP : θ ∈ intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ)))
    (hθQ : θ ∈ intrinsicInterior ℝ (Q : Set _)) :
    (d.truncationMap ℒ hkl).bchGroupMap ((d.reconstructFinite h ℒ g).label Q) =
      (d.reconstructFinite h ℒ ((d.truncationMap ℒ hkl).bchGroupMap g)).label P := by
  rw [d.reconstructFinite_label h ℒ g Q hθQ,
    d.reconstructFinite_label h ℒ _ P hθP]
  exact truncationMap_signFactorizationEquiv_symm ℒ _ d hkl g 0

variable {L' : Type*} [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L']
  [IsScalarTower ℚ R L'] (ℳ : N → Submodule R L')
  [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]

/-- Finite middle-factor reconstruction commutes with degree-preserving
coefficient changes, as an equality on the same geometric arrangement. -/
theorem map_reconstructFinite
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (g : d.truncatedGroup ℒ k) :
    (d.reconstructFinite h ℒ g).map f =
      d.reconstructFinite h ℳ ((f.truncatedMap k (by simp)).bchGroupMap g) := by
  ext P
  · rw [KSComplex.map_degree]
    rfl
  · obtain ⟨θ, hθ⟩ := d.arrangementCellPoint h
      ⟨P, (d.arrangementComplex h k).mem_cells_of_mem_walls P.property⟩
    rw [KSComplex.map_label, d.reconstructFinite_label h ℒ g P hθ,
      d.reconstructFinite_label h ℳ _ P hθ]
    exact f.truncatedMap_signFactorizationEquiv_symm _ k g 0

end Mei.PositiveDegrees
