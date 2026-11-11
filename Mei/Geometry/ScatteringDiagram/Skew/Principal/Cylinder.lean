/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Initial
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Cylinder.Scat
public import Mei.Geometry.ScatteringDiagram.Skew.Hyperplane

/-!
# Projected principal diagrams and principal cylinders

Take the principal degree lattice `L_pr = M° × N_uf`, the principal positive monoid of
`r(n) = (p₁*(n), n)` and the projected principal wall spaces, with spatial map
`ρ = pr₁ : L_pr → M°`. Since the projected principal graph wall spaces are the
`DirectedWallSpaces.project` of the principal graph wall spaces along `pr₁`, every
projected principal wall lifts by pullback of supports to a principal cylinder
`𝔡 × (N_uf)_ℝ` with `ρ = id`, and the normal `κ(n)⟨n,-⟩` pulls back to `κ(n)ν_n`.
The generic cylinder API then preserves signed path products, consistency,
refinements, equivalence and outgoing completions.

On a wall of degree `r(n)`, the projected spatial velocity is `-p₁*(n)` and the cylinder
velocity is `-r(n)`, and `r(n) ∈ rec(𝔡 × (N_uf)_ℝ) ↔ p₁*(n) ∈ rec(𝔡)`. The adapted
polynomial input on the principal lattice is exactly the cylinder of its projected
counterpart, whose wall at the unfrozen index `k` is the full hyperplane
`ker κ(e_k)⟨e_k,-⟩` in `M°_ℝ`. Hence the outgoing scattering class of the principal input
is the cylinder of the projected scattering class.

For a radical degree `n`, with `{-, n} = 0`, `p₁*(n) = 0`, so `ρ(r(n)) = 0` and every
projected principal wall of degree `r(n)` has zero spatial velocity and is incoming, as is its
principal cylinder. For the zero form every degree is radical. If the form vanishes on the
unfrozen sublattice, in particular for the zero form, both adapted polynomial inputs are
consistent by `SkewLatticeDatum.consistent_of_forall_form_eq_zero`.

The principal realization follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2. We use
`SkewLatticeDatum.projectedPrincipalGraphWallSpaces`, `DirectedWall.cylinder`,
`DirectedDiagram.cylinder`, `DirectedDiagram.cylinder_scat`,
`SkewLatticeDatum.AdaptedBasis.adaptedPolynomialInput` and
`SkewLatticeDatum.consistent_of_forall_form_eq_zero`.
-/

public section

noncomputable section

open Set

namespace Mei.SkewLatticeDatum

variable {N R V E : Type*} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (D : SkewLatticeDatum N)

section Wall

variable [Module.Free ℤ N] {D} {d : PositiveDegrees D.unfrozen}
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  {i : Module.Dual ℤ D.sublattice →+ V} {j : D.unfrozen →+ E}
  {h : TauCeti.Toric.IsIntegralLattice i}
  (h' : TauCeti.Toric.IsIntegralLattice j)
  (W : DirectedWall (d := D.principalPositiveDegrees d) h
    (D.projectedPrincipalGraphWallSpaces (R := R) d))
  {n : D.unfrozen} (hn : W.ray.generator = D.principalEmbedding n)

include hn in
/-- A projected principal wall of degree `r(n)` moves with spatial velocity `-p₁*(n)`. -/
theorem projectedPrincipal_direction_eq : W.direction = -i (D.principalCharacter n) := by
  rw [DirectedWall.direction_def, hn]
  simp

include hn in
/-- Its principal cylinder moves with velocity `-r(n)`, the full principal exponent. -/
theorem principalCylinder_direction_eq :
    (W.cylinder h').direction = -(i.prodMap j) (D.principalEmbedding n) := by
  rw [DirectedWall.direction_def, DirectedWall.cylinder_ray, hn, AddMonoidHom.id_apply]

include hn in
/-- The principal cylinder of a wall of degree `r(n)` is incoming exactly when `p₁*(n)`
is a recession direction of the projected support:
`r(n) ∈ rec(𝔡 × (N_uf)_ℝ) ↔ p₁*(n) ∈ rec(𝔡)`. -/
theorem principalCylinder_incoming_iff :
    (W.cylinder h').Incoming ↔ i (D.principalCharacter n) ∈ recessionCone ℝ W.support := by
  rw [DirectedWall.cylinder_incoming_iff, DirectedWall.incoming_iff, ← mem_recessionCone, hn]
  simp

include hn in
/-- The principal cylinder of a wall of degree `r(n)` is outgoing exactly when `p₁*(n)`
is not a recession direction of the projected support. -/
theorem principalCylinder_outgoing_iff :
    (W.cylinder h').Outgoing ↔ i (D.principalCharacter n) ∉ recessionCone ℝ W.support := by
  rw [DirectedWall.cylinder_outgoing_iff, DirectedWall.outgoing_iff, hn]
  simp

include hn in
/-- A projected principal wall of radical degree `r(n)`, with `{-, n} = 0`, has zero spatial
velocity, since `ρ(r(n)) = p₁*(n) = 0`. -/
theorem projectedPrincipal_direction_eq_zero_of_form_flip_eq_zero
    (hrad : D.form.flip n = 0) : W.direction = 0 := by
  rw [projectedPrincipal_direction_eq W hn, (D.principalCharacter_eq_zero_iff n).mpr hrad,
    map_zero, neg_zero]

include hn in
/-- A projected principal wall of radical degree `r(n)` and its principal cylinder are
incoming, whatever their supports. -/
theorem incoming_of_form_flip_eq_zero (hrad : D.form.flip n = 0) :
    W.Incoming ∧ (W.cylinder h').Incoming := by
  have hW : W.Incoming := W.incoming_of_geometricDirection_eq_zero (by
    rw [hn]
    simp [(D.principalCharacter_eq_zero_iff n).mpr hrad])
  exact ⟨hW, (DirectedWall.cylinder_incoming_iff W h').mpr hW⟩

include hn in
/-- For the zero form, every projected principal wall of degree `r(n)` has zero spatial
velocity, since `ρ(r(n)) = p₁*(n) = 0`. -/
theorem projectedPrincipal_direction_eq_zero_of_form_eq_zero (hform : D.form = 0) :
    W.direction = 0 :=
  projectedPrincipal_direction_eq_zero_of_form_flip_eq_zero W hn (by ext; simp [hform])

include hn in
/-- For the zero form, every projected principal wall of degree `r(n)` and its principal
cylinder are incoming, whatever their supports. -/
theorem incoming_of_form_eq_zero (hform : D.form = 0) :
    W.Incoming ∧ (W.cylinder h').Incoming :=
  incoming_of_form_flip_eq_zero h' W hn (by ext; simp [hform])

end Wall

namespace AdaptedBasis

variable [Module.Free ℤ N] {D} {ι : Type*} (B : D.AdaptedBasis ι)
  (ℓ : B.unfrozenIndex → ℕ) (a : ∀ i, Fin (ℓ i) → R)
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  {i : Module.Dual ℤ D.sublattice →+ V} (h : TauCeti.Toric.IsIntegralLattice i)

local notation "𝒅" => B.unfrozenBasis.positiveDegrees
local notation "𝓟" => D.projectedPrincipalGraphWallSpaces (R := R) 𝒅

/-- The adapted polynomial input on the character lattice `M°`: at each unfrozen index `k`
the full hyperplane `ker κ(e_k)⟨e_k,-⟩` with the normalized polynomial label, on the
projected principal wall spaces. Its wall at `k` has spatial velocity `-p₁*(e_k)`, possibly
zero. -/
def projectedAdaptedPolynomialInput :
    DirectedDiagram (V := V) (d := D.principalPositiveDegrees 𝒅) h (𝓟) B.unfrozenIndex :=
  DirectedDiagram.ofFinite (h := h) (H := 𝓟) fun k =>
    DirectedWall.ofAffineHyperplane (V := V) h (𝓟)
      (D.projectedPrincipalNormal (B.unfrozenBasis k)).toAddMonoidHom
      (by
        intro hz
        exact (B.unfrozenBasis.ne_zero k) ((D.projectedPrincipalNormal_eq_zero_iff _).mp
          (LinearMap.toAddMonoidHom_injective hz))) 0
      ((B.unfrozenBasis.positiveDegreesRay k).graph D.principalCharacter.toAddMonoidHom)
      (by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, ← AddMonoidHom.comp_apply,
          D.projectedPrincipalNormal_comp_fst]
        apply Int.cast_injective (α := ℚ)
        simp only [SupportedRay.graph_generator, Module.Basis.positiveDegreesRay_generator,
          LinearMap.toAddMonoidHom_coe]
        rw [← D.principalEmbedding_apply, D.cast_principalNormal_principalEmbedding]
        simp)
      ⟨B.polynomialWallLabel ℓ a k, by
        rw [DirectedWallSpaces.project_wallGroup, D.projectedPrincipalNormal_comp_fst]
        exact (B.polynomialWallLabel ℓ a k).property⟩

/-- The coorientation at `k` is the projected principal normal `κ(e_k)⟨e_k,-⟩`. -/
@[simp]
theorem projectedAdaptedPolynomialInput_normal (k : B.unfrozenIndex) :
    ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).normal =
      (D.projectedPrincipalNormal (B.unfrozenBasis k)).toAddMonoidHom := by
  simp [projectedAdaptedPolynomialInput]

/-- The degree ray at `k` is the principal ray through `r(e_k)`. -/
@[simp]
theorem projectedAdaptedPolynomialInput_ray (k : B.unfrozenIndex) :
    ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).ray =
      (B.unfrozenBasis.positiveDegreesRay k).graph D.principalCharacter.toAddMonoidHom := by
  simp [projectedAdaptedPolynomialInput]

/-- The support is the full hyperplane of the projected principal normal. -/
@[simp]
theorem projectedAdaptedPolynomialInput_support (k : B.unfrozenIndex) :
    ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).support =
      (h.realCharacter (D.projectedPrincipalNormal (B.unfrozenBasis k)).toAddMonoidHom).ker := by
  ext
  simp [projectedAdaptedPolynomialInput]

/-- The projected input carries the same normalized polynomial label. -/
@[simp]
theorem projectedAdaptedPolynomialInput_label (k : B.unfrozenIndex) :
    ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).label =
      B.polynomialWallLabel ℓ a k := by
  simp [projectedAdaptedPolynomialInput]

/-- The projected wall at `k` moves with spatial velocity `-p₁*(e_k)`. -/
theorem projectedAdaptedPolynomialInput_direction (k : B.unfrozenIndex) :
    ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).direction =
      -i (D.principalCharacter (B.unfrozenBasis k)) :=
  projectedPrincipal_direction_eq _ (n := B.unfrozenBasis k) (by simp)

/-- All projected input walls are incoming, including those of zero spatial velocity. -/
@[simp]
theorem projectedAdaptedPolynomialInput_incoming (k : B.unfrozenIndex) :
    ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).Incoming := by
  simp [projectedAdaptedPolynomialInput]

/-- The projected input satisfies the full-hyperplane hypothesis of outgoing scattering. -/
theorem projectedAdaptedPolynomialInput_full (k : B.unfrozenIndex) :
    ∃ c : ℝ, ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).support =
      {x | h.realCharacter ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).normal x
        = c} := by
  refine ⟨0, ?_⟩
  rw [B.projectedAdaptedPolynomialInput_support, B.projectedAdaptedPolynomialInput_normal]
  exact Set.ext fun _ => LinearMap.mem_ker

variable {j : D.unfrozen →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)

/-- The adapted polynomial input on the principal lattice `M° × N_uf` is the principal
cylinder of the projected adapted polynomial input on `M°`: at each `k` the hyperplane of
`κ(e_k)ν_k` is the cylinder over the hyperplane of `κ(e_k)⟨e_k,-⟩`, with the same ray and
label. -/
theorem cylinder_projectedAdaptedPolynomialInput :
    (B.projectedAdaptedPolynomialInput ℓ a h).cylinder h' =
      B.adaptedPolynomialInput ℓ a (h.prod h') := by
  refine DirectedDiagram.ext (funext fun k => DirectedWall.ext ?_ ?_ ?_ ?_)
  · simp
  · simp
  · rw [DirectedDiagram.cylinder_wall, DirectedWall.cylinder_support,
      B.adaptedPolynomialInput_support, ← D.projectedPrincipalNormal_comp_fst,
      (h.prod h').realCharacter_comp h (AddMonoidHom.fst (Module.Dual ℤ D.sublattice) D.unfrozen)
        (LinearMap.fst ℝ V E) (fun _ => rfl)]
    ext x
    simp
  · simp

/-- Projected and principal adapted polynomial inputs have the same outgoing scattering
class after adjoining the unrestricted `(N_uf)_ℝ` coordinates: the outgoing completion of
the principal input is the principal cylinder of the completion of the projected input. -/
theorem cylinder_scat_projectedAdaptedPolynomialInput
    [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)] :
    DirectedDiagram.Class.cylinder h'
        ((B.projectedAdaptedPolynomialInput ℓ a h).Scat
          (B.projectedAdaptedPolynomialInput_full ℓ a h)) =
      (B.adaptedPolynomialInput ℓ a (h.prod h')).Scat
        (B.adaptedPolynomialInput_full ℓ a (h.prod h')) := by
  rw [DirectedDiagram.cylinder_scat]
  simp only [B.cylinder_projectedAdaptedPolynomialInput ℓ a h h']

/-- For the zero form the projected input walls have zero spatial velocity. -/
theorem projectedAdaptedPolynomialInput_direction_eq_zero_of_form_eq_zero
    (hform : D.form = 0) (k : B.unfrozenIndex) :
    ((B.projectedAdaptedPolynomialInput (V := V) ℓ a h).wall k).direction = 0 :=
  projectedPrincipal_direction_eq_zero_of_form_eq_zero _ (n := B.unfrozenBasis k) (by simp) hform

/-- If the form vanishes on the unfrozen sublattice, the projected adapted polynomial input is
consistent. -/
theorem projectedAdaptedPolynomialInput_consistent_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0) :
    (B.projectedAdaptedPolynomialInput (V := V) ℓ a h).Consistent :=
  D.consistent_of_forall_form_eq_zero hform _ (B.projectedAdaptedPolynomialInput_full ℓ a h)

/-- If the form vanishes on the unfrozen sublattice, the adapted polynomial input on the
principal lattice is consistent. Pairings with frozen vectors are unrestricted. -/
theorem adaptedPolynomialInput_consistent_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0)
    {p : Module.Dual ℤ D.sublattice × D.unfrozen →+ V} (hp : TauCeti.Toric.IsIntegralLattice p) :
    (B.adaptedPolynomialInput (V := V) ℓ a hp).Consistent :=
  D.consistent_of_forall_form_eq_zero hform _ (B.adaptedPolynomialInput_full ℓ a hp)

end AdaptedBasis

end Mei.SkewLatticeDatum
