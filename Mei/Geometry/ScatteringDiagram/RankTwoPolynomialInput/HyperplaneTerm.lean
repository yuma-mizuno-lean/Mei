/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat

/-!
# Rank-two polynomial inputs as polynomial function walls on hyperplanes

Let `I` be a rank-two polynomial input on positive degree data `(L, P, δ)`, with projection
`π : L → M`, incoming lines `{ν_j = c_j}`, `j ∈ ι`, and wall functions
`f_j = 1 + ∑_n c_{j,n} z^n`, and let `s` be a finite set of lines. Keeping the terms of the lines
in `s` gives a `HyperplaneTermInput` with finitely many terms
(`RankTwoPolynomialInput.toHyperplaneTermInput`): the hyperplane `j ∈ ι` is the cylinder
`{x ∈ L_ℝ | ν_j(π x) = c_j}` with the normal `ν_j ∘ π` and `ρ = id`, and the term `c_{j,n} z^n`
of a line `j ∈ s` lies on the hyperplane `j` with exponent `n`; the lines outside `s` carry no
terms.

On a line `i` that lies in `s` or has no term, the wall function of the hyperplane `i` is `f_i`
(`RankTwoPolynomialInput.tangentInitialFunction_eq_toHyperplaneTermInput`), so its label is the
unsplit label `exp(log(f_i) ∂_{ν_i ∘ π})`
(`RankTwoPolynomialInput.label_toHyperplaneTermInput`), and the walls of the ray presentation over
the line `i` are the walls of the incoming diagram
(`RankTwoPolynomialInput.incomingDiagram_wall_eq`). Hence:

* if every line with a term lies in `s`, for instance `s = univ` for finitely many lines, the
  incoming diagram is the ray presentation (`RankTwoPolynomialInput.incomingDiagram_eq_diagram`);
* if `s` contains the lines `linesAtOrder k` with a term of degree at most `k`, both diagrams keep
  only walls over the lines of `s` at order `k`, so they are equivalent at order `k`
  (`RankTwoPolynomialInput.incomingDiagram_levelEquivalent_diagram`), and the order-`k`
  scattering class of `I` is that of the finite input
  (`RankTwoPolynomialInput.projection_scat_incomingDiagram`).

Only the lines are restricted: the terms of degree larger than `k` of the lines in `s` are kept.
The rank-two polynomial inputs, with only finitely many lines nontrivial at each order, are those
of Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, Theorem 9.9
(arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput

open _root_.AddMonoidAlgebra DirectedDiagram

variable {L M ι R V : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι) (s : Finset ι)

-- An `abbrev`, so that its normals are the cylinder normals `I.wallNormal` up to reducible
-- unfolding: then the walls of its ray presentation are indexed by `IncomingIndex`, and its labels
-- live in the tangent coefficient algebras of `initialLabel`.
/-- The lines of a rank-two polynomial input as polynomial function walls on hyperplanes, keeping
the terms of the lines in a finite set `s`: the hyperplane `j ∈ ι` is the cylinder over the line
`j`, with the normal `ν_j ∘ π`, the offset `c_j` and `ρ = id`, and the term `c_{j,n} z^n` of a
line `j ∈ s` lies on the hyperplane `j` with exponent `n`. -/
abbrev toHyperplaneTermInput :
    HyperplaneTermInput d (AddMonoidHom.id L) ι (Σ j : s, I.exponents j) where
  normal := I.wallNormal
  normal_ne_zero := I.wallNormal_ne_zero
  offset := I.offset
  wallIndex α := α.1.val
  exponent α := α.2
  exponent_mem α := I.mem_monoid_of_mem_exponents α.2.property
  exponent_ne_zero α := I.ne_zero_of_mem_exponents α.2.property
  normal_exponent α := I.wallNormal_eq_zero_of_mem_exponents α.2.property

/-- The hyperplanes are cooriented by the cylinder normals `ν_j ∘ π`. -/
@[simp]
theorem toHyperplaneTermInput_normal : (I.toHyperplaneTermInput s).normal = I.wallNormal :=
  (rfl)

/-- The hyperplanes have the offsets of the lines. -/
@[simp]
theorem toHyperplaneTermInput_offset : (I.toHyperplaneTermInput s).offset = I.offset :=
  (rfl)

/-- The term `c_{j,n} z^n` lies on the hyperplane `j`. -/
@[simp]
theorem toHyperplaneTermInput_wallIndex (α : Σ j : s, I.exponents j) :
    (I.toHyperplaneTermInput s).wallIndex α = α.1 :=
  (rfl)

/-- The term `c_{j,n} z^n` has the exponent `n`. -/
@[simp]
theorem toHyperplaneTermInput_exponent (α : Σ j : s, I.exponents j) :
    (I.toHyperplaneTermInput s).exponent α = α.2 :=
  (rfl)

variable [CommRing R] [DecidableEq ι] (c : I.Variable → R)

/-- If the line `i` lies in `s` or has no term, the wall function of the hyperplane `i`, with the
coefficients `c_{j,n}`, is the wall function `f_i = 1 + ∑_n c_{i,n} z^n` of the line. -/
theorem tangentInitialFunction_eq_toHyperplaneTermInput {i : ι}
    (hi : (I.exponents i).Nonempty → i ∈ s) :
    I.tangentInitialFunction c i = 1 + ∑ α : (I.toHyperplaneTermInput s).Term i,
      single ((I.toHyperplaneTermInput s).tangentExponent (R := R) i α) (c ⟨α.1.1.val, α.1.2⟩) := by
  rw [tangentInitialFunction_def]
  congr 1
  by_cases his : i ∈ s
  · -- The term `n` of the line `i ∈ s` is the term `⟨i, n⟩` of the hyperplane `i`.
    refine Fintype.sum_bijective (fun n => ⟨⟨⟨i, his⟩, n⟩, rfl⟩) ⟨fun n n' hn => ?_, ?_⟩ _ _
      fun n => congrArg (single · _) (Subtype.ext (by simp))
    · simpa using hn
    · rintro ⟨⟨⟨j, hj⟩, n⟩, rfl⟩
      exact ⟨n, rfl⟩
  · -- Otherwise the line and the hyperplane have no terms.
    have : IsEmpty (I.exponents i) :=
      Finset.isEmpty_coe_sort.mpr (Finset.not_nonempty_iff_eq_empty.mp (mt hi his))
    have : IsEmpty ((I.toHyperplaneTermInput s).Term i) :=
      ⟨fun α => his (by simp [← α.property])⟩
    rw [Fintype.sum_empty, Fintype.sum_empty]

variable [DecidableEq L] [Algebra ℚ R]

/-- If the line `i` lies in `s` or has no term, the label of the hyperplane `i`, with the
coefficients `c_{j,n}`, is the unsplit label `exp(log(f_i) ∂_{ν_i ∘ π})` of the line. -/
theorem label_toHyperplaneTermInput {i : ι} (hi : (I.exponents i).Nonempty → i ∈ s) :
    (I.toHyperplaneTermInput s).label (fun α => c ⟨α.1, α.2⟩) i = I.initialLabel c i := by
  simp only [HyperplaneTermInput.label_def, initialLabel_def,
    I.tangentInitialFunction_eq_toHyperplaneTermInput s c hi]

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) [Module.Free ℤ L]

/-- Over a line that lies in `s` or has no term, the walls of the incoming diagram are the walls
of the ray presentation of the terms of the lines in `s`, with the coefficients `c_{j,n}`. -/
theorem incomingDiagram_wall_eq (x : I.IncomingIndex) (hx : (I.exponents x.1).Nonempty → x.1 ∈ s) :
    (I.incomingDiagram h c).wall x =
      ((I.toHyperplaneTermInput s).diagram h fun α => c ⟨α.1, α.2⟩).wall x := by
  apply DirectedWall.ext <;> simp [I.label_toHyperplaneTermInput s c hx]

/-- If every line with a term lies in `s`, the incoming diagram is the ray presentation of the
terms of the lines in `s`, with the coefficients `c_{j,n}`. This applies to `s = univ` when there
are finitely many lines. -/
theorem incomingDiagram_eq_diagram (hs : ∀ j, (I.exponents j).Nonempty → j ∈ s) :
    I.incomingDiagram h c = (I.toHyperplaneTermInput s).diagram h fun α => c ⟨α.1, α.2⟩ :=
  DirectedDiagram.ext (funext fun x => I.incomingDiagram_wall_eq s c h x (hs x.1))

/-- If `s` contains every line with a term of degree at most `k`, the incoming diagram is
equivalent at order `k` to the ray presentation of the terms of the lines in `s`, with the
coefficients `c_{j,n}`. -/
theorem incomingDiagram_levelEquivalent_diagram {k : ℕ} (hs : ∀ j ∈ I.linesAtOrder k, j ∈ s) :
    (I.incomingDiagram h c).LevelEquivalent
      ((I.toHyperplaneTermInput s).diagram h fun α => c ⟨α.1, α.2⟩) k := by
  -- At order `k`, both diagrams have their active walls over the lines of `s`, where their walls
  -- agree; so both are equivalent to their common restriction to these walls.
  let S : Set I.IncomingIndex := {x | x.1 ∈ s}
  have hD : (I.incomingDiagram h c).active k ⊆ S := fun x hx =>
    hs x.1 (I.mem_linesAtOrder_of_mem_active h c hx)
  have hE : ((I.toHyperplaneTermInput s).diagram h fun α => c ⟨α.1, α.2⟩).active k ⊆ S :=
    fun x hx => by
      obtain ⟨α, hα, -⟩ :=
        HyperplaneTermInput.exists_wallIndex_eq_and_degree_le_of_mem_active _ h _ hx
      simp [S, ← hα]
  have hDE : (I.incomingDiagram h c).restrict S =
      ((I.toHyperplaneTermInput s).diagram h fun α => c ⟨α.1, α.2⟩).restrict S :=
    DirectedDiagram.ext (funext fun x => by
      simpa using I.incomingDiagram_wall_eq s c h x fun _ => x.property)
  refine ((I.incomingDiagram h c).levelEquivalent_restrict hD).trans ?_
  rw [hDE]
  exact (levelEquivalent_restrict _ hE).symm

/-- If `s` contains every line with a term of degree at most `k`, the order-`k` scattering class
of the incoming diagram is that of the ray presentation of the terms of the lines in `s`, with the
coefficients `c_{j,n}`. -/
theorem projection_scat_incomingDiagram {k : ℕ} (hs : ∀ j ∈ I.linesAtOrder k, j ∈ s) :
    ((I.incomingDiagram h c).Scat (I.incomingDiagram_full h c)).projection k =
      (((I.toHyperplaneTermInput s).diagram h fun α => c ⟨α.1, α.2⟩).Scat
        fun _ => ofHyperplaneRayFactors_full ..).projection k :=
  projection_scat_eq_of_levelEquivalent _ _ (I.incomingDiagram_levelEquivalent_diagram s c h hs)

end Mei.RankTwoPolynomialInput
