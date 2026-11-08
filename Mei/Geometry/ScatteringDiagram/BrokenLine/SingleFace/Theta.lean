/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.FunctionWall
public import Mei.Geometry.ScatteringDiagram.Coefficient.Hyperplane

/-!
# The theta section of one function wall

Let `ker f` be a hyperplane cooriented by `f` and carrying the function wall `1 - z` of weight
`f ∘ v` on a graded coefficient algebra, so that a label `θ` of a group acting on the
algebra multiplies a weight-one element `a` by `1 - z` (`functionWallAction`). For an incoming
datum `a` of relative degree zero and normal weight one, entering from the half-space `0 < f`,
the actual weighted evaluation of the cutoff decorated rays at an off-wall endpoint `Q` is
`hyperplaneFactor f θ Q • θ • a`: it is `a` where `0 < f Q` and `a - a z` where `f Q < 0`.

The evaluation is therefore the family of chamber values of a global section of the
coefficient local system of the one-hyperplane diagram, `hyperplaneSection`, and this is the
unique section with these values (`existsUnique_section_value_eq_cutoffDecoratedEvaluation`):
the facet equation `s(Q⁺) = θ⁻¹ • s(Q⁻)` of the local system is the identity
`θ • a = a - a z` for the function wall.

Restricting the section to an open on the negative side of the wall, such as `{f < -1}`, which
the wall misses, still gives the value `a - a z` (`value_restrict_eq_sub_mul_of_forall_lt`). This
differs from the incoming coefficient `a` as soon as `a z ≠ 0`
(`value_restrict_ne_of_mul_ne_zero`), while the trivial wall `z = 0` gives the value `a` on both
sides: the section remembers the incoming tails and bends outside the open. The hypotheses are
met by the group `A ≃ₐ[R] A` acting on `A`, with `θ = functionWallAction 𝒜 u`.

The function wall is that of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, Example 2.1(i) (arXiv:1503.06183v5), and the single-face broken lines and their
gluing are those of Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Mei.GradedAlgebra Mei.FiniteWallDiagram

namespace Mei

section Evaluation

variable {R A Γ V H : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq Γ]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] {ℳ : Γ → Submodule R A}
  [DirectSum.Decomposition ℳ] [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Γ]
  {d : PositiveDegrees Γ} {a : ℳ 0} {v : Γ → V} {ε : Unit → SignType} {f : V →L[ℝ] ℝ} {k : ℕ}
  [Group H] [MulAction H A]

/-- Weighted evaluation through one function wall `1 - z`, at an off-wall endpoint `Q`, is the
crossing factor of `Q` times `θ • a`, where the label `θ` acts as the function wall. This is `a`
on the source side, where the crossing factor is `θ⁻¹`, and `a - a z` on the far side. -/
theorem cutoffDecoratedEvaluation_functionWall_one_sub_eq_hyperplaneFactor (θ : H) (u : (𝒜 0)ˣ)
    (z : A) {n : Γ} (hθ : ∀ x : A, θ • x = functionWallAction 𝒜 u x) (hu : (u : A) = 1 - z)
    (hz : (a : A) * z ∈ ℳ n) (hn : n ∈ d.cutoff k) (w : Γ → ℤ) (hw : ∀ q, ℳ q ≤ 𝒜 (w q))
    (hν : ∀ q, f (v q) = w q) (hν0 : f (v 0) = 1) (hε : ε () = 1) {Q : V} (hQ : f Q ≠ 0) :
    cutoffDecoratedEvaluation d ℳ (fun _ : Unit => (functionWallAction 𝒜 u).toLinearMap) a v
        (fun _ : Unit => f) (fun _ : Unit => 0) ε (fun _ : Unit => {x | f x = 0})
        (fun _ : Unit => {x | f x = 0}) (fun _ : Unit => (∅ : Set V))
        {x | 0 < (f x - 0) / f (v 0)} k Q =
      hyperplaneFactor f θ Q • θ • (a : A) := by
  have hw0 : w 0 = 1 := by
    have := hν 0
    rw [hν0] at this
    exact_mod_cast this.symm
  have hap : θ • (a : A) = (a : A) - a * z := by
    rw [hθ]
    exact functionWallAction_apply_of_mem_one_sub 𝒜 u hu (hw0 ▸ hw 0 a.2)
  rcases hQ.lt_or_gt with hQ | hQ
  · rw [cutoffDecoratedEvaluation_functionWall_one_sub_of_neg 𝒜 u z hu hz hn w hw hν hν0 hε
      (by simpa using hQ), hap, hyperplaneFactor_def, ite_eq_right hQ.not_gt, one_smul]
  · rw [cutoffDecoratedEvaluation_singleFace_of_pos (Set.empty_subset _)
      (by rwa [hν0, sub_zero, div_one]), hyperplaneFactor_def, ite_eq_left hQ, inv_smul_smul]

end Evaluation

section Section

variable {N R A Γ V H : Type*} [AddCommGroup N] [CommRing R] [CommRing A] [Algebra R A]
  [DecidableEq Γ] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] {ℳ : Γ → Submodule R A}
  [DirectSum.Decomposition ℳ] [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Γ]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {d : PositiveDegrees Γ} {a : ℳ 0}
  {v : Γ → V} {ε : Unit → SignType} {f : V →L[ℝ] ℝ}
  {hf : Toric.IsRationalFunctional h f.toLinearMap} (hf0 : f ≠ 0) {k : ℕ}
  [Group H] [MulAction H A]

/-- The chamber values of the theta section of one function wall `1 - z` are the actual weighted
evaluations of the cutoff decorated rays: the section `hyperplaneSection` with value `θ • a` on
the negative side of the wall takes at every off-wall point the evaluation at that point, and is
determined by these values. -/
theorem existsUnique_section_value_eq_cutoffDecoratedEvaluation (θ : H) (u : (𝒜 0)ˣ) (z : A)
    {n : Γ} (hθ : ∀ x : A, θ • x = functionWallAction 𝒜 u x) (hu : (u : A) = 1 - z)
    (hz : (a : A) * z ∈ ℳ n) (hn : n ∈ d.cutoff k) (w : Γ → ℤ) (hw : ∀ q, ℳ q ≤ 𝒜 (w q))
    (hν : ∀ q, f (v q) = w q) (hν0 : f (v 0) = 1) (hε : ε () = 1) :
    ∃! s : ((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem A).presheaf.obj (op ⊤),
      ∀ x hx, ((hyperplaneDiagram hf hf0 θ).coefficientTransport A).value s x hx =
        cutoffDecoratedEvaluation d ℳ (fun _ : Unit => (functionWallAction 𝒜 u).toLinearMap) a v
          (fun _ : Unit => f) (fun _ : Unit => 0) ε (fun _ : Unit => {x | f x = 0})
          (fun _ : Unit => {x | f x = 0}) (fun _ : Unit => (∅ : Set V))
          {x | 0 < (f x - 0) / f (v 0)} k x.val.val := by
  have hval : ∀ x : (FinitePolyhedralComplex.hyperplaneComplex f hf).coefficientPoints,
      hyperplaneFactor f θ x.val.val • θ • (a : A) =
        cutoffDecoratedEvaluation d ℳ (fun _ : Unit => (functionWallAction 𝒜 u).toLinearMap) a v
          (fun _ : Unit => f) (fun _ : Unit => 0) ε (fun _ : Unit => {x | f x = 0})
          (fun _ : Unit => {x | f x = 0}) (fun _ : Unit => (∅ : Set V))
          {x | 0 < (f x - 0) / f (v 0)} k x.val.val := fun x =>
    (cutoffDecoratedEvaluation_functionWall_one_sub_eq_hyperplaneFactor 𝒜 θ u z hθ hu hz hn w hw
      hν hν0 hε (fun h0 => x.property
        ⟨_, (FinitePolyhedralComplex.mem_hyperplaneComplex_walls_iff hf hf0).mpr rfl⟩ h0)).symm
  refine ⟨hyperplaneSection hf hf0 θ (θ • (a : A)), fun x hx => ?_, fun s hs => ?_⟩
  · rw [value_hyperplaneSection, hval]
  · refine ((hyperplaneDiagram hf hf0 θ).coefficientTransport A).section_ext fun x hx => ?_
    rw [hs x hx, value_hyperplaneSection, hval]

/-- The restriction of the theta section of one function wall `1 - z` to an open of the regular
locus on the negative side of the wall takes the value `a - a z`, though the wall misses the
open. For `U = {f < -1}` this is the restriction check: the section retains the incoming tails
and bends outside `U`. -/
theorem value_restrict_eq_sub_mul_of_forall_lt (θ : H) (u : (𝒜 0)ˣ) (z : A) {n : Γ}
    (hu : (u : A) = 1 - z) (hz : (a : A) * z ∈ ℳ n) (hn : n ∈ d.cutoff k) (w : Γ → ℤ)
    (hw : ∀ q, ℳ q ≤ 𝒜 (w q)) (hν : ∀ q, f (v q) = w q) (hν0 : f (v 0) = 1) (hε : ε () = 1)
    {U : Opens (FinitePolyhedralComplex.hyperplaneComplex f hf).regularSpace}
    (hU : ∀ x ∈ U, f x.val < 0)
    {s : ((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem A).presheaf.obj (op ⊤)}
    (hs : ∀ x hx, ((hyperplaneDiagram hf hf0 θ).coefficientTransport A).value s x hx =
      cutoffDecoratedEvaluation d ℳ (fun _ : Unit => (functionWallAction 𝒜 u).toLinearMap) a v
        (fun _ : Unit => f) (fun _ : Unit => 0) ε (fun _ : Unit => {x | f x = 0})
        (fun _ : Unit => {x | f x = 0}) (fun _ : Unit => (∅ : Set V))
        {x | 0 < (f x - 0) / f (v 0)} k x.val.val)
    (x : (FinitePolyhedralComplex.hyperplaneComplex f hf).coefficientPoints) (hx : x.val ∈ U) :
    ((hyperplaneDiagram hf hf0 θ).coefficientTransport A).value
        (((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem A).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op s) x hx = (a : A) - a * z := by
  rw [DenseBasisTransport.value_restrict, hs,
    cutoffDecoratedEvaluation_functionWall_one_sub_of_neg 𝒜 u z hu hz hn w hw hν hν0 hε (hU _ hx)]

/-- The restriction of the theta section of one function wall `1 - z` to an open on the negative
side of the wall is not the incoming coefficient `a`, the value for the diagram without wall,
as soon as `a z ≠ 0`. -/
theorem value_restrict_ne_of_mul_ne_zero (θ : H) (u : (𝒜 0)ˣ) (z : A) {n : Γ}
    (hu : (u : A) = 1 - z) (hz : (a : A) * z ∈ ℳ n) (hn : n ∈ d.cutoff k) (w : Γ → ℤ)
    (hw : ∀ q, ℳ q ≤ 𝒜 (w q)) (hν : ∀ q, f (v q) = w q) (hν0 : f (v 0) = 1) (hε : ε () = 1)
    {U : Opens (FinitePolyhedralComplex.hyperplaneComplex f hf).regularSpace}
    (hU : ∀ x ∈ U, f x.val < 0)
    {s : ((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem A).presheaf.obj (op ⊤)}
    (hs : ∀ x hx, ((hyperplaneDiagram hf hf0 θ).coefficientTransport A).value s x hx =
      cutoffDecoratedEvaluation d ℳ (fun _ : Unit => (functionWallAction 𝒜 u).toLinearMap) a v
        (fun _ : Unit => f) (fun _ : Unit => 0) ε (fun _ : Unit => {x | f x = 0})
        (fun _ : Unit => {x | f x = 0}) (fun _ : Unit => (∅ : Set V))
        {x | 0 < (f x - 0) / f (v 0)} k x.val.val)
    (haz : (a : A) * z ≠ 0)
    (x : (FinitePolyhedralComplex.hyperplaneComplex f hf).coefficientPoints) (hx : x.val ∈ U) :
    ((hyperplaneDiagram hf hf0 θ).coefficientTransport A).value
        (((hyperplaneDiagram hf hf0 θ).coefficientLocalSystem A).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op s) x hx ≠ (a : A) := by
  rw [value_restrict_eq_sub_mul_of_forall_lt 𝒜 hf0 θ u z hu hz hn w hw hν hν0 hε hU hs x hx]
  exact fun h => haz (by simpa using h)

end Section

end Mei
