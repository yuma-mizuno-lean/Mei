/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Covariance
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat.Relative
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Covariance.Basic

/-!
# Affine covariance of the relative scattering class

A split extension `h = g ⋉ I` is transported by compatible integral affine and graded Lie
coordinate changes of its two wall spaces, which agree on degrees and tangent lattices and
intertwine the projection and the section. The positive degree functions of source and
target may differ.

Such a transport carries a relative completion problem to a relative completion problem
(`IsRelativeCompletionInput.image`), commutes with lifting along the section
(`DirectedDiagram.image_map`) and with adjoining the ideal inputs
(`DirectedDiagram.image_append`), and carries the relative scattering class to the relative
scattering class of the transported problem (`image_relativeScat`). The finite-order form
`projection_image_relativeScat` compares the order-`k` classes through any source order
covering the modulus of the coordinate change.

The pure-birth clause of a relative outgoing completion is stated for the degree function
of its own side, and a change of degree function moves the birth order. So the image of a
relative outgoing completion is only an outgoing completion of the transported initial
walls; the comparison goes through `outgoingCompletion_unique`, as in
`IsOutgoingCompletion.equivalent_image`. The completions are those of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Theorem 2.6, run over an ideal as in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
[arXiv:1411.1394v2](https://arxiv.org/abs/1411.1394v2), Appendix C.3.
-/

public section

noncomputable section

namespace Mei

universe u

variable {Γ Γ₁ Λ Λ₁ R V V₁ : Type*} {L L' L₁ L₁' : Type u} {ι κ : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ₁] [AddCommGroup Λ] [AddCommGroup Λ₁]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L₁] [LieAlgebra R L₁] [LieAlgebra ℚ L₁] [IsScalarTower ℚ R L₁]
  [LieRing L₁'] [LieAlgebra R L₁'] [LieAlgebra ℚ L₁'] [IsScalarTower ℚ R L₁']
  [DecidableEq Γ] [DecidableEq Γ₁]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
  {ρ : Γ →+ Λ} {ρ₁ : Γ₁ →+ Λ₁} {d : PositiveDegrees Γ} {d₁ : PositiveDegrees Γ₁}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  {ℒ₁ : Γ₁ → Submodule R L₁} {ℳ₁ : Γ₁ → Submodule R L₁'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  [GradedLieAlgebra ℒ₁] [GradedLieAlgebra ℳ₁] [IsPositiveGrading d₁ ℒ₁]
  [IsPositiveGrading d₁ ℳ₁]
  {i : Λ →+ V} {i₁ : Λ₁ →+ V₁}
  {h : TauCeti.Toric.IsIntegralLattice i} {h₁ : TauCeti.Toric.IsIntegralLattice i₁}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  {H₁ : DirectedWallSpaces ρ₁ ℒ₁} {H₁' : DirectedWallSpaces ρ₁ ℳ₁}
  (e : Toric.IntegralAffineEquiv h h₁)
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d₁) H H₁)
  (E' : DirectedWallSpaces.CoordinateChange (d := d) (e := d₁) H' H₁')
  (hE : E.tangentEquiv = e.latticeEquiv) (hE' : E'.tangentEquiv = e.latticeEquiv)
  (hdeg : E'.degreeEquiv = E.degreeEquiv)
  {sec : GradedLieHom (PositiveDegreeMap.id d) ℳ ℒ}
  {hs : ∀ n m, ∀ x ∈ H'.wall n m, sec x ∈ H.wall n m}
  {sec₁ : GradedLieHom (PositiveDegreeMap.id d₁) ℳ₁ ℒ₁}
  {hs₁ : ∀ n m, ∀ x ∈ H₁'.wall n m, sec₁ x ∈ H₁.wall n m}
  (hsec : ∀ x, E.lieEquiv (sec x) = sec₁ (E'.lieEquiv x))

namespace DirectedWall

include hdeg hsec in
/-- Lifting a wall along a section commutes with coordinate changes that intertwine the
section. -/
theorem image_map (W : DirectedWall (d := d) h H') :
    (W.map sec hs).image e E hE = (W.image e E' hE').map sec₁ hs₁ := by
  have hcomm : (E.gradedLieHom.comp sec).completedMap =
      (sec₁.comp E'.gradedLieHom).completedMap :=
    GradedLieHom.completedMap_eq_of_toLieHom_eq _ _ (by ext x; simpa using hsec x)
  have hlabel := DFunLike.congr_fun hcomm W.label
  simp only [GradedLieHom.completedMap_comp, MonoidHom.comp_apply] at hlabel
  apply DirectedWall.ext
  · simp [hE, hE']
  · exact SupportedRay.ext (by simp [hdeg])
  · simp
  · simpa using hlabel

end DirectedWall

namespace DirectedDiagram

include hdeg hsec in
/-- Lifting a diagram along a section commutes with coordinate changes that intertwine the
section. -/
theorem image_map (G : DirectedDiagram (d := d) h H' ι) :
    (G.map sec hs).image e E hE = (G.image e E' hE').map sec₁ hs₁ := by
  apply DirectedDiagram.ext
  funext j
  simp only [image_wall, map_wall]
  exact DirectedWall.image_map e E E' hE hE' hdeg hsec (G.wall j)

/-- Coordinate changes transport an adjoined family wall by wall. -/
theorem image_append (D : DirectedDiagram (d := d) h H ι) (D' : DirectedDiagram (d := d) h H κ) :
    (D.append D').image e E hE = (D.image e E hE).append (D'.image e E hE) := by
  apply DirectedDiagram.ext
  funext j
  rcases j with j | j <;> simp only [image_wall, append_wall_inl, append_wall_inr]

section Relative

variable {π : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ}
  {π₁ : GradedLieHom (PositiveDegreeMap.id d₁) ℒ₁ ℳ₁}
  {hπ : ∀ n m, ∀ x ∈ H.wall n m, π x ∈ H'.wall n m}
  {hπ₁ : ∀ n m, ∀ x ∈ H₁.wall n m, π₁ x ∈ H₁'.wall n m}
  {G : DirectedDiagram (d := d) h H' ι} {W : DirectedDiagram (d := d) h H κ}

/-- Coordinate changes that intertwine the projection carry a relative completion problem
to a relative completion problem. -/
theorem IsRelativeCompletionInput.image (hfπ : ∀ x, π₁ (E.lieEquiv x) = E'.lieEquiv (π x))
    (hGW : IsRelativeCompletionInput π G W) :
    IsRelativeCompletionInput π₁ (G.image e E' hE') (W.image e E hE) where
  consistent := hGW.consistent.image
  exists_support_eq_hyperplane := W.image_fullHyperplane hGW.exists_support_eq_hyperplane e E hE
  completedMap_label_eq_one j := by
    have hcomm : (π₁.comp E.gradedLieHom).completedMap = (E'.gradedLieHom.comp π).completedMap :=
      GradedLieHom.completedMap_eq_of_toLieHom_eq _ _ (by ext x; simpa using hfπ x)
    have := DFunLike.congr_fun hcomm (W.wall j).label
    simp only [GradedLieHom.completedMap_comp, MonoidHom.comp_apply,
      hGW.completedMap_label_eq_one j, map_one] at this
    simpa using this

variable [Module.Free ℤ Γ] [Module.Free ℤ Γ₁]

include hdeg hsec in
/-- The relative scattering class commutes with coordinate changes that intertwine the
projection and the section. -/
theorem image_relativeScat (hsπ : ∀ x, π (sec x) = x) (hsπ₁ : ∀ x, π₁ (sec₁ x) = x)
    (hfπ : ∀ x, π₁ (E.lieEquiv x) = E'.lieEquiv (π x))
    (hGW : IsRelativeCompletionInput π G W) :
    Class.image e E hE (relativeScat π hπ sec hs G W hsπ hGW) =
      relativeScat π₁ hπ₁ sec₁ hs₁ (G.image e E' hE') (W.image e E hE) hsπ₁
        (hGW.image e E E' hE hE' hfπ) := by
  obtain ⟨η, F, hF, hc⟩ := relativeScat_spec hπ hs hsπ hGW
  obtain ⟨η', F', hF', hc'⟩ := relativeScat_spec hπ₁ hs₁ hsπ₁ (hGW.image e E E' hE hE' hfπ)
  rw [hc, hc', Class.image_toClass, toClass_eq_iff]
  have hwall : (fun j => (((G.map sec hs).append W).wall j).image e E hE) =
      (((G.image e E' hE').map sec₁ hs₁).append (W.image e E hE)).wall :=
    (funext fun j => image_wall _ e E hE j).symm.trans (congrArg DirectedDiagram.wall
      (by rw [image_append, image_map e E E' hE hE' hdeg hsec]))
  have hF₀ := hF.isOutgoingCompletion.image (e := e) (E := E) (hE := hE)
  rw [hwall] at hF₀
  exact outgoingCompletion_unique hF₀ hF'.isOutgoingCompletion

include hdeg hsec in
/-- The order-`k` relative scattering class of the transported problem is the transport of the
class at any source order `a` covering the modulus of the coordinate change. -/
theorem projection_image_relativeScat (hsπ : ∀ x, π (sec x) = x) (hsπ₁ : ∀ x, π₁ (sec₁ x) = x)
    (hfπ : ∀ x, π₁ (E.lieEquiv x) = E'.lieEquiv (π x))
    (hGW : IsRelativeCompletionInput π G W) (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a) :
    (relativeScat π₁ hπ₁ sec₁ hs₁ (G.image e E' hE') (W.image e E hE) hsπ₁
        (hGW.image e E E' hE hE' hfπ)).projection k =
      LevelClass.image e E hE k ha ((relativeScat π hπ sec hs G W hsπ hGW).projection a) := by
  rw [← image_relativeScat e E E' hE hE' hdeg hsec hsπ hsπ₁ hfπ hGW,
    Class.projection_image_of_le e E hE k ha]

end Relative

end DirectedDiagram

end Mei
