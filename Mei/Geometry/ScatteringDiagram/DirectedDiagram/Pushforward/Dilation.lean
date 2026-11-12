/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.GermLabel
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Scat

/-!
# Dilations and germ labels along rays

The dilation `DirectedWall.Pushforward.dilation` by a positive rational `q` moves every support
`S` to `q • S` and keeps normals, rays and labels. It fixes a diagram whose supports are
invariant under rescaling (`DirectedDiagram.pushforward_dilation_eq_self`), for instance an input
of full hyperplanes through the origin. Since forming the scattering class commutes with
pushforward (`DirectedDiagram.pushforward_scat`), every representative `E` of the scattering class
of such a *central* input is equivalent to all its dilations
(`DirectedDiagram.equivalent_pushforward_dilation_of_toClass_eq_scat`). The germ label of the
dilation at `q • θ` is the germ label of `E` at `θ`
(`DirectedDiagram.germLabel_pushforward_dilation`).

The main result is that the germ label is constant along open rays in a linear hyperplane `A`
and is the same for all representatives. If `E` and `F` represent the scattering class of a
central input, `θ` is a generic point of `A` for `E`, and `t • θ`, `t > 0`, is a generic point of
`A` for `F`, then the germ labels of `F` at `t • θ` and of `E` at `θ` agree in every direction
outside the direction of `A` (`DirectedDiagram.germLabel_smul_eq_of_toClass_eq_scat`, from
`DirectedDiagram.germLabel_smul_eq_of_equivalent_dilation`).

So for a central input the *wall function on a ray* of its completion, in the sense of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2),
is one element of the completed group, independent of the representative and of the generic
point on the ray. Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
Theorem 9.5 (arXiv:2503.03719v1), compares these wall functions on `ℝ_{≤0}m°` for two lattices.
-/

public section

open TauCeti (singularSupport)

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Filter Topology Pointwise Mei.Convex

namespace Mei.DirectedDiagram

universe u v

variable {Γ Λ R V : Type*} {L : Type v} {ι κ κ' : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι)

section Dilation

variable {q : ℚ} (hq : 0 < q)

/-- A dilation by `q` fixes a diagram all of whose supports are invariant under rescaling
by `q`. -/
theorem pushforward_dilation_eq_self
    (hD : ∀ j, (q : ℝ) • (D.wall j).support = (D.wall j).support) :
    D.pushforward (DirectedWall.Pushforward.dilation d h H q hq) = D :=
  DirectedDiagram.ext (funext fun j => by
    rw [pushforward_wall, DirectedWall.pushforward_dilation_eq_self _ hq (hD j)])

variable {D} in
/-- A point outside the singular support of the walls active at order `k` is moved by the
dilation by `q` to a point outside the singular support of the dilated walls. -/
theorem smul_notMem_singularSupport_pushforward_dilation (k : ℕ) {θ : V}
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) :
    (q : ℝ) • θ ∉ singularSupport (fun j :
      (D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).active k =>
        ((D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).wall j).support) := by
  simpa using D.notMem_singularSupport_pushforward
    (DirectedWall.Pushforward.dilation d h H q hq) k (by simp) hθ

/-- The combined label of the dilation by `q` at `q • θ` is the combined label at `θ`, in every
direction. -/
theorem combinedLabel_pushforward_dilation (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hθ' : (q : ℝ) • θ ∉ singularSupport (fun j :
      (D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).active k =>
        ((D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).wall j).support)) :
    (D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).combinedLabel k ((q : ℝ) • θ)
      v hθ' = D.combinedLabel k θ v hθ := by
  have he := D.combinedLabel_pushforward (DirectedWall.Pushforward.dilation d h H q hq) k
    (by simp) θ v hθ
  simp only [DirectedWall.Pushforward.dilation_lieHom_lieTruncatedMap, LieHom.bchGroupMap_id,
    MonoidHom.id_apply, DirectedWall.Pushforward.dilation_spatialMap_apply,
    DirectedWall.Pushforward.dilation_spatialMap_linear_apply] at he
  rwa [combinedLabel_smul_pos _ _ _ _ _ (by exact_mod_cast hq)] at he

variable {D} in
/-- A point regular for `D` is moved by the dilation by `q` to a point regular for the dilated
diagram. -/
theorem IsRegular.smul_pushforward_dilation {θ : V} (hθ : D.IsRegular θ) :
    (D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).IsRegular ((q : ℝ) • θ) :=
  (isRegular_iff _ _).mpr fun k =>
    smul_notMem_singularSupport_pushforward_dilation hq k (hθ.notMem_singularSupport k)

/-- The germ label of the dilation by `q` at `q • θ` is the germ label at `θ`, in every
direction. -/
theorem germLabel_pushforward_dilation {θ : V} (v : V) (hθ : D.IsRegular θ)
    (hθ' : (D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).IsRegular
      ((q : ℝ) • θ)) :
    (D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).germLabel ((q : ℝ) • θ) v hθ' =
      D.germLabel θ v hθ :=
  TauCeti.CompletedGroup.ext fun k => by
    rw [projection_germLabel, projection_germLabel, combinedLabel_pushforward_dilation]

variable {D} in
/-- A generic point `θ` of an affine subspace `A` through the origin is moved by the dilation by
`q` to a generic point `q • θ` of `A` for the dilated diagram. -/
theorem IsGenericPoint.smul_pushforward_dilation {A : AffineSubspace ℝ V} (hA : (0 : V) ∈ A)
    {θ : V} (hθ : D.IsGenericPoint A θ) :
    (D.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).IsGenericPoint A
      ((q : ℝ) • θ) := by
  have hmap :
      A.map (DirectedWall.Pushforward.dilation d h H q hq).spatialMap.toAffineEquiv.toAffineMap =
        A := by
    have hsmul (c : ℝ) {x : V} (hx : x ∈ A) : c • x ∈ A := by
      simpa using AffineSubspace.smul_vsub_vadd_mem A c hx hA hA
    ext y
    simp only [AffineSubspace.mem_map, AffineEquiv.coe_toAffineMap, ContinuousAffineEquiv.coe_coe,
      DirectedWall.Pushforward.dilation_spatialMap_apply]
    refine ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hsmul _ hx, fun hy => ⟨(q : ℝ)⁻¹ • y, hsmul _ hy, ?_⟩⟩
    rw [smul_inv_smul₀ (by exact_mod_cast hq.ne')]
  simpa [hmap] using hθ.pushforward (DirectedWall.Pushforward.dilation d h H q hq)

/-- **Germ labels along rays of a dilation-invariant class.** Let `E` and `F` be equivalent
directed diagrams, with `E` equivalent to its dilation by every positive rational. Let `A` be an
affine hyperplane through the origin, `θ` a generic point of `A` for `E`, and `t • θ`, with
`t > 0`, a generic point of `A` for `F`. Then the germ label of `F` at `t • θ` is the germ label of
`E` at `θ`, in every direction outside the direction of `A`. -/
theorem germLabel_smul_eq_of_equivalent_dilation {E : DirectedDiagram (d := d) h H κ}
    {F : DirectedDiagram (d := d) h H κ'} (hEF : E.Equivalent F)
    (hdil : ∀ (q : ℚ) (hq : 0 < q),
      (E.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).Equivalent E)
    {A : AffineSubspace ℝ V} (hA : (0 : V) ∈ A)
    (hdim : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V)
    {θ v : V} {t : ℝ} (ht : 0 < t) (hθ : E.IsGenericPoint A θ)
    (htθ : F.IsGenericPoint A (t • θ)) (hv : v ∉ A.direction) :
    F.germLabel (t • θ) v htθ.isRegular = E.germLabel θ v hθ.isRegular := by
  refine TauCeti.CompletedGroup.ext fun k => ?_
  /- At order `k`, the germ label of `F` is constant on `A` near `t • θ`. Pick a positive
  rational `q` with `q • θ` in that neighbourhood. The dilation of `E` by `q` is generic at
  `q • θ`, where it has the germ label of `E` at `θ`, and its germ label is constant on `A` near
  `q • θ`. It is equivalent to `F`, so a common generic point of both in the two neighbourhoods
  links the two germ labels. -/
  obtain ⟨U, hU, htU, hUF⟩ := mem_nhdsWithin.mp (htθ.eventually_projection_germLabel_eq k)
  obtain ⟨q, hqU, hq⟩ : ∃ q : ℚ, (q : ℝ) • θ ∈ U ∧ 0 < q := by
    have ho : IsOpen ({s : ℝ | s • θ ∈ U} ∩ Ioi 0) :=
      (hU.preimage (continuous_id.smul continuous_const)).inter isOpen_Ioi
    obtain ⟨q, hqU, hq⟩ := Rat.denseRange_cast.exists_mem_open ho ⟨t, htU, ht⟩
    exact ⟨q, hqU, by exact_mod_cast mem_Ioi.mp hq⟩
  have hθq := hθ.smul_pushforward_dilation hq hA
  obtain ⟨U', hU', hqU', hU'E⟩ := mem_nhdsWithin.mp (hθq.eventually_projection_germLabel_eq k)
  obtain ⟨ζ, ⟨⟨hζU, hζU'⟩, hζA⟩, hζE, hζF⟩ := exists_isGenericPoint_pair
    (E.pushforward (DirectedWall.Pushforward.dilation d h H q hq)) F
    (ContinuousAffineEquiv.refl ℝ V) A hdim (hU.inter hU') ⟨_, ⟨hqU, hqU'⟩, hθq.mem⟩
  have hζF' : F.IsGenericPoint A ζ := by simpa using hζF
  rw [← hUF ⟨hζU, hζA⟩ hζF'.isRegular v, ← ((hdil q hq).trans hEF).germLabel_eq hζE hζF' hv,
    hU'E ⟨hζU', hζA⟩ hζE.isRegular v, germLabel_pushforward_dilation]

end Dilation

section Scat

variable [Module.Free ℤ Γ]

/-- **Dilation invariance of the scattering class.** Let `I` be an input of full hyperplanes
through the origin. Every representative of its scattering class is equivalent to its dilation
by every positive rational `q`. -/
theorem equivalent_pushforward_dilation_of_toClass_eq_scat (I : DirectedDiagram (d := d) h H ι)
    (hI : ∀ j, (I.wall j).support = {x | h.realCharacter (I.wall j).normal x = 0})
    {E : DirectedDiagram (d := d) h H κ}
    (hE : E.toClass = I.Scat fun j => ⟨0, hI j⟩) {q : ℚ} (hq : 0 < q) :
    (E.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).Equivalent E := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  -- Hyperplanes through the origin are invariant under rescaling.
  have hII : (I.pushforward (DirectedWall.Pushforward.dilation d h H q hq)).Equivalent I := by
    rw [I.pushforward_dilation_eq_self hq fun j => by
      ext x
      rw [hI j, Set.mem_smul_set_iff_inv_smul_mem₀ hq', Set.mem_ofPred_eq, Set.mem_ofPred_eq,
        map_smul, smul_eq_mul, mul_eq_zero, or_iff_right (inv_ne_zero hq')]]
  refine (toClass_eq_iff _ _).mp ?_
  rw [← Class.pushforward_toClass, hE, pushforward_scat,
    scat_eq_of_equivalent _ (fun j => ⟨0, hI j⟩) hII]

/-- **Germ labels on rays of a scattering class.** Let `I` be an input of full hyperplanes
through the origin, and let `E` and `F` represent its scattering class. Let `A` be an affine
hyperplane through the origin, `θ` a generic point of `A` for `E`, and `t • θ`, with `t > 0`, a
generic point of `A` for `F`. Then the germ label of `F` at `t • θ` is the germ label of `E` at
`θ`, in every direction outside the direction of `A`. So the germ label of the class along each
open ray of `A` is independent of the representative and of the generic point on the ray. -/
theorem germLabel_smul_eq_of_toClass_eq_scat (I : DirectedDiagram (d := d) h H ι)
    (hI : ∀ j, (I.wall j).support = {x | h.realCharacter (I.wall j).normal x = 0})
    {E : DirectedDiagram (d := d) h H κ} (hE : E.toClass = I.Scat fun j => ⟨0, hI j⟩)
    {F : DirectedDiagram (d := d) h H κ'} (hF : F.toClass = I.Scat fun j => ⟨0, hI j⟩)
    {A : AffineSubspace ℝ V} (hA : (0 : V) ∈ A)
    (hdim : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V)
    {θ v : V} {t : ℝ} (ht : 0 < t) (hθ : E.IsGenericPoint A θ)
    (htθ : F.IsGenericPoint A (t • θ)) (hv : v ∉ A.direction) :
    F.germLabel (t • θ) v htθ.isRegular = E.germLabel θ v hθ.isRegular :=
  germLabel_smul_eq_of_equivalent_dilation ((toClass_eq_iff _ _).mp (hE.trans hF.symm))
    (fun _ hq => equivalent_pushforward_dilation_of_toClass_eq_scat I hI hE hq) hA hdim ht hθ htθ
    hv

end Scat

end Mei.DirectedDiagram
