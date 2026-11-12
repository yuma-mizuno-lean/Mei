/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Pushforward

/-!
# Finite alphabet lifts of polynomial function walls

Fix cooriented affine hyperplanes in a lattice `M` and a finite family `E` of terms
`c_α z^{m_α}`, the term `α` lying on the hyperplane `wallIndex α` with `m_α` tangent to it. The
alphabet input (`HyperplaneTermInput.finiteAlphabet`) has the letters `v_α = (m_α, e_α)` of
`PositiveDegrees.finiteAlphabet` as exponents, so that the hyperplane `i` carries the alphabet
wall function `1 + ∑_{wallIndex α = i} c_α z^{v_α}`.

Given positive degree data `(L, P, δ)`, a projection `π : L → M` and an additive map `τ` with
`τ v_α = n_α ∈ P ∖ {0}` and `π n_α = m_α`, an input on the alphabet is lifted along `τ`
(`HyperplaneTermInput.liftFiniteAlphabet`); the lift of the alphabet input has exponents `n_α`
(`HyperplaneTermInput.liftFiniteAlphabet_finiteAlphabet_exponent`). The pushforward of the ray
presentation of the alphabet wall functions along
`DirectedWall.Pushforward.ofFiniteAlphabetLift` is equivalent to the ray presentation of
`1 + ∑ c_α z^{n_α}` in `P`
(`HyperplaneTermInput.diagram_pushforward_ofFiniteAlphabetLift_equivalent`), and the scattering
classes correspond (`HyperplaneTermInput.pushforward_scat_liftFiniteAlphabet`).
Distinct letters lie on distinct rays of the alphabet (`PositiveDegrees.letterRay_injective`),
while their images may lie on one ray of `P`; the equivalence regroups the image rays into the
ray factors of `1 + ∑ c_α z^{n_α}`.

The walls are full affine hyperplanes; walls supported on proper polyhedral subsets of
hyperplanes are not treated. If the first coordinates of the exponents on each hyperplane are
positive multiples of one direction, so are the projections of the lifted exponents
(`HyperplaneTermInput.liftFiniteAlphabet_projectedDirection`). The grouping and positivity of
the lifted wall functions are
`HyperplaneTermInput.isPositiveWallRepresentative_liftFiniteAlphabet_diagram`, in
`Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Grouping`. Not formalized here: the maps of
shifted modules induced by the lift, and the identification `z^{v_{i,s}} ↦ p_{i,s} z^{s w_i}` for
BLM polynomial inputs. The degree inequality of the lift is
`PositiveDegrees.finiteAlphabet_degree_lt`.

The finite alphabet lift follows Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, §9.2 (arXiv:2503.03719v1).
-/

public section

open TauCeti (PositiveDegrees)

noncomputable section

namespace Mei.HyperplaneTermInput

open DirectedWall TauCeti.PositiveDegrees DirectedDiagram

universe u

variable {R M ι E L : Type u} {V : Type*} [CommRing R] [AddCommGroup M] [Fintype E]
  [DecidableEq E] [AddCommGroup L]

section Alphabet

variable (μ : ι → M →+ ℤ) (hμ : ∀ i, μ i ≠ 0) (a : ι → ℝ) (w : E → ι) (m : E → M)
  (hm : ∀ α, μ (w α) (m α) = 0)

/-- The alphabet input: the hyperplanes `{μ_i = a_i}` of `M`, and the term `α` on the hyperplane
`w α` with the letter `v_α = (m_α, e_α)` as exponent. -/
def finiteAlphabet :
    HyperplaneTermInput (PositiveDegrees.finiteAlphabet m) (AddMonoidHom.fst M (E → ℤ)) ι E where
  normal := μ
  normal_ne_zero := hμ
  offset := a
  wallIndex := w
  exponent := letter m
  exponent_mem := letter_mem m
  exponent_ne_zero := letter_ne_zero m
  normal_exponent α := by simpa using hm α

/-- The alphabet input has the normals `μ_i`. -/
@[simp]
theorem finiteAlphabet_normal : (finiteAlphabet μ hμ a w m hm).normal = μ := by
  simp [finiteAlphabet]

/-- The alphabet input has the offsets `a_i`. -/
@[simp]
theorem finiteAlphabet_offset : (finiteAlphabet μ hμ a w m hm).offset = a := by
  simp [finiteAlphabet]

/-- The alphabet input places the term `α` on the hyperplane `w α`. -/
@[simp]
theorem finiteAlphabet_wallIndex : (finiteAlphabet μ hμ a w m hm).wallIndex = w := by
  simp [finiteAlphabet]

/-- The alphabet input has the letters as exponents. -/
@[simp]
theorem finiteAlphabet_exponent : (finiteAlphabet μ hμ a w m hm).exponent = letter m := by
  simp [finiteAlphabet]

end Alphabet

variable {m : E → M} {f : PositiveDegrees L} {τ : M × (E → ℤ) →+ L}
  (hτ : ∀ α, τ (letter m α) ∈ f.monoid) (hτ0 : ∀ α, τ (letter m α) ≠ 0)
  {π : L →+ M} (hπ : ∀ α, π (τ (letter m α)) = m α)
  (I : HyperplaneTermInput (PositiveDegrees.finiteAlphabet m) (AddMonoidHom.fst M (E → ℤ)) ι E)

include hπ in
/-- On allowed degrees of the finite alphabet, `π` after the finite alphabet lift is the first
projection to `M`. -/
theorem projection_finiteAlphabetLift {x : M × (E → ℤ)}
    (hx : x ∈ (PositiveDegrees.finiteAlphabet m).monoid) :
    π (PositiveDegrees.finiteAlphabetLift m hτ hτ0 x) = AddMonoidHom.fst M (E → ℤ) x := by
  rw [finiteAlphabetLift_apply]
  exact eq_fst_of_eq_sum m (σ := π.comp τ) hπ ((mem_finiteAlphabet_monoid m).mp hx).2

/-- An input on the finite alphabet lifted along `τ`: the same hyperplanes, with exponents
`τ x_α`. -/
def liftFiniteAlphabet : HyperplaneTermInput f π ι E :=
  I.map (PositiveDegrees.finiteAlphabetLift m hτ hτ0) (AddMonoidHom.id M)
    (fun _ hx => projection_finiteAlphabetLift hτ hτ0 hπ hx) I.normal
    fun _ => AddMonoidHom.comp_id _

/-- The lifted input has the hyperplane normals of the input. -/
@[simp]
theorem liftFiniteAlphabet_normal : (I.liftFiniteAlphabet hτ hτ0 hπ).normal = I.normal := by
  simp [liftFiniteAlphabet]

/-- The lifted input has the hyperplane offsets of the input. -/
@[simp]
theorem liftFiniteAlphabet_offset : (I.liftFiniteAlphabet hτ hτ0 hπ).offset = I.offset := by
  simp [liftFiniteAlphabet]

/-- The lifted input places each term on the hyperplane of the input. -/
@[simp]
theorem liftFiniteAlphabet_wallIndex :
    (I.liftFiniteAlphabet hτ hτ0 hπ).wallIndex = I.wallIndex := by
  simp [liftFiniteAlphabet]

/-- The lifted input has the exponents `τ x_α`. -/
@[simp]
theorem liftFiniteAlphabet_exponent (α : E) :
    (I.liftFiniteAlphabet hτ hτ0 hπ).exponent α = τ (I.exponent α) := by
  simp [liftFiniteAlphabet]

/-- If the first coordinates of the exponents `x_α` on each hyperplane `i` of an input on the
finite alphabet are positive multiples of `u_i`, the lifted exponents `τ x_α` project under `π`
to the same positive multiples. -/
theorem liftFiniteAlphabet_projectedDirection (u : ι → M)
    (hu : ∀ α, ∃ b : ℕ, 0 < b ∧ (I.exponent α).1 = b • u (I.wallIndex α)) (α : E) :
    ∃ b : ℕ, 0 < b ∧ π ((I.liftFiniteAlphabet hτ hτ0 hπ).exponent α) =
      b • u ((I.liftFiniteAlphabet hτ hτ0 hπ).wallIndex α) := by
  rw [liftFiniteAlphabet_exponent, liftFiniteAlphabet_wallIndex,
    ← PositiveDegrees.finiteAlphabetLift_apply m hτ hτ0,
    projection_finiteAlphabetLift hτ hτ0 hπ (I.exponent_mem α)]
  exact hu α

/-- The lift of the alphabet input has the exponents `n_α = τ v_α`. -/
theorem liftFiniteAlphabet_finiteAlphabet_exponent (μ : ι → M →+ ℤ) (hμ : ∀ i, μ i ≠ 0)
    (a : ι → ℝ) (w : E → ι) (hm : ∀ α, μ (w α) (m α) = 0) (α : E) :
    ((finiteAlphabet μ hμ a w m hm).liftFiniteAlphabet hτ hτ0 hπ).exponent α =
      τ (letter m α) := by
  simp

variable [Algebra ℚ R] [Module.Free ℤ L] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {j : M →+ V} (g : TauCeti.Toric.IsIntegralLattice j)

local notation "Pτ" => Pushforward.ofFiniteAlphabetLift (R := R) (g := g) hτ hτ0 hπ

/-- The lifted input is the input mapped along the degree map of the pushforward data. -/
theorem map_ofFiniteAlphabetLift_degreeMap
    (hPT : ∀ x ∈ (PositiveDegrees.finiteAlphabet m).monoid,
      π ((Pτ).degreeMap x) = AddMonoidHom.id M (AddMonoidHom.fst M (E → ℤ) x)) :
    I.map (Pτ).degreeMap (AddMonoidHom.id M) hPT I.normal (fun _ => AddMonoidHom.comp_id _) =
      I.liftFiniteAlphabet hτ hτ0 hπ := by
  rw [liftFiniteAlphabet]
  exact map_congr fun α => by rw [Pushforward.ofFiniteAlphabetLift_degreeMap]

variable [Module.Free ℤ M] [DecidableEq M] [DecidableEq ι] [DecidableEq L] (c : E → R)

/-- The pushforward of the ray presentation of an input on the finite alphabet along the finite
alphabet lift is equivalent to the ray presentation of the lifted input. -/
theorem diagram_pushforward_ofFiniteAlphabetLift_equivalent :
    ((I.diagram g c).pushforward (Pτ)).Equivalent
      ((I.liftFiniteAlphabet hτ hτ0 hπ).diagram g c) := by
  have hPT : ∀ x ∈ (PositiveDegrees.finiteAlphabet m).monoid,
      π ((Pτ).degreeMap x) = AddMonoidHom.id M (AddMonoidHom.fst M (E → ℤ) x) := fun x hx => by
    rw [Pushforward.ofFiniteAlphabetLift_degreeMap]
    exact projection_finiteAlphabetLift hτ hτ0 hπ hx
  rw [← I.map_ofFiniteAlphabetLift_degreeMap hτ hτ0 hπ g hPT]
  refine I.diagram_pushforward_equivalent _ _ _ (Pτ) (fun _ _ y hy => ?_) hPT c
    (fun _ => Pushforward.ofFiniteAlphabetLift_normalMap hτ hτ0 hπ _)
    (fun _ _ => by simp)
  rw [Pushforward.coe_ofFiniteAlphabetLift_lieHom_of_homogeneous hτ hτ0 hπ y _ hy,
    Pushforward.ofFiniteAlphabetLift_degreeMap, finiteAlphabetLift_apply]

/-- Pushing forward the scattering class of an input on the finite alphabet along the finite
alphabet lift gives the scattering class of the lifted input. -/
theorem pushforward_scat_liftFiniteAlphabet :
    Class.pushforward (Pτ) ((I.diagram g c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((I.liftFiniteAlphabet hτ hτ0 hπ).diagram g c).Scat
        (fun _ => ofHyperplaneRayFactors_full ..) :=
  ((I.diagram g c).pushforward_scat _ _).trans (DirectedDiagram.scat_eq_of_equivalent _ _
    (I.diagram_pushforward_ofFiniteAlphabetLift_equivalent hτ hτ0 hπ g c))

end Mei.HyperplaneTermInput
