/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Filtration
public import TauCeti.Combinatorics.Quiver.BoundedPaths
public import Mathlib.Basic.Finite.Sigma
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite inventories of complete component histories

A finite family of encounter paths has only finitely many surviving component
histories, uniformly on a finitely generated incoming submodule. The chamber
modules and their degree types may vary along the paths and need not be finite.
An encounter bound in a finite quiver supplies the required finite path family.

A component filtration with a common vanishing order and bounded unmarked runs
also gives finiteness without a separately supplied encounter bound. Only admitted
histories need satisfy the run bound. Thus geometric incidence, source admission
and avoidance conditions may select histories before this result is applied.
All encounters and intermediate degrees remain part of the inventory, including
unchanged degrees and changes invisible in spatial directions.

The construction reuses `TauCeti.Quiver.finite_boundedPaths` and the shared
uniform support theorem `Quiver.Path.exists_uniform_historySupport_of_fg`.
For transfers, use the existing zero-extended `GradedCorrespondence.totalTransfer`
as the arrow maps; inadmissible source pieces then vanish automatically. The
finite encounter-tree interpretation follows Gross–Hacking–Siebert, *Theta
functions on varieties with effective anti-canonical class*, Proposition 3.5
and Lemma 3.7 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei

open Quiver

variable {Q : Type*} [Quiver Q] {a : Q}
  {R : Type*} [Semiring R] {M : Q → Type*}
  [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]

/-- A finite encounter inventory has only finitely many complete degree histories
surviving on a finitely generated incoming submodule. The inventory is uniform
over all inputs in that submodule, without finite generation of chamber modules. -/
theorem finite_histories_of_finite_paths {s : Set (Σ b : Q, Path a b)}
    (hs : s.Finite) (P : Submodule R (M a)) (hP : P.FG) :
    {z : Σ b : Q, Σ p : Path a b, p.Degrees ι |
      (⟨z.1, z.2.1⟩ : Σ b : Q, Path a b) ∈ s ∧
        ∃ x ∈ P, z.2.1.homogeneousHistory T ℳ z.2.2 x ≠ 0}.Finite := by
  have hf (p : Σ b : Q, Path a b) :
      {d : p.2.Degrees ι | ∃ x ∈ P, p.2.homogeneousHistory T ℳ d x ≠ 0}.Finite := by
    obtain ⟨S, hS⟩ := p.2.exists_uniform_historySupport_of_fg T ℳ P hP
    refine S.finite_toSet.subset ?_
    rintro d ⟨x, hx, hd⟩
    by_contra hnot
    exact hd (hS d hnot x hx)
  exact ((hs.sigma fun p _ => hf p).image
    (Equiv.sigmaAssoc (fun b (p : Path a b) => p.Degrees ι))).subset (by
      rintro ⟨b, p, d⟩ ⟨hp, hd⟩
      exact ⟨⟨⟨b, p⟩, d⟩, ⟨hp, hd⟩, rfl⟩)

variable [Finite Q] [∀ b c : Q, Finite (b ⟶ c)]

/-- Across all encounter paths of length at most `L`, one finite inventory retains
every complete component history for the whole finitely generated input range. -/
theorem finite_bounded_histories (L : ℕ) (P : Submodule R (M a)) (hP : P.FG) :
    {z : Σ b : Q, Σ p : Path a b, p.Degrees ι |
      z.2.1.length ≤ L ∧ ∃ x ∈ P, z.2.1.homogeneousHistory T ℳ z.2.2 x ≠ 0}.Finite := by
  have hf (b : Q) : {p : Path a b | p.length ≤ L}.Finite := by
    exact @Set.toFinite _ _ (TauCeti.Quiver.finite_boundedPaths L a b)
  simpa only [Set.mem_sigma_iff, Set.mem_univ, Set.mem_ofPred_eq, true_and] using
    finite_histories_of_finite_paths T ℳ (Set.finite_univ.sigma fun b _ => hf b) P hP

/-- A fixed incoming coefficient has finitely many surviving complete histories
across all bounded encounter paths, even with infinite-dimensional chambers and
infinitely many degrees. No finiteness assumption on its homogeneous piece is needed. -/
theorem finite_bounded_historySupport (L : ℕ) (x : M a) :
    {z : Σ b : Q, Σ p : Path a b, p.Degrees ι |
      z.2.1.length ≤ L ∧ z.2.1.homogeneousHistory T ℳ z.2.2 x ≠ 0}.Finite := by
  refine (finite_bounded_histories T ℳ L (R ∙ x) (Submodule.fg_span_singleton x)).subset ?_
  intro z hz
  exact ⟨hz.1, x, Submodule.subset_span (Set.mem_singleton x), hz.2⟩

variable (F : ∀ q, ModuleFiltration R (M q))
  (w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ)

/-- A nilpotent component filtration gives a finite inventory of all admitted,
surviving histories, with no encounter bound in the conclusion's indexing type.
Only admitted surviving histories need have bounded zero-weight runs. -/
theorem finite_histories_of_componentTransfersRaise
    (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := w))
    (i₀ : ι a) (P : Submodule R (M a)) (hP : P.FG) (hPi : P ≤ ℳ a i₀)
    {r h : ℕ} (hr : ∀ b, (F b).submodule r = ⊥)
    (admit : (Σ b : Q, Σ p : Path a b, p.Degrees ι) → Prop)
    (hbound : ∀ b (p : Path a b) (d : p.Degrees ι), admit ⟨b, p, d⟩ →
      (∃ x ∈ P, p.homogeneousHistory T ℳ d x ≠ 0) →
        Path.IsZeroRunBounded (GradedVertex.componentWeight w) h (Path.Degrees.liftPath i₀ p d)) :
    {z : Σ b : Q, Σ p : Path a b, p.Degrees ι |
      admit z ∧ ∃ x ∈ P, z.2.1.homogeneousHistory T ℳ z.2.2 x ≠ 0}.Finite := by
  refine (finite_bounded_histories T ℳ (r * h + r - 1) P hP).subset ?_
  rintro ⟨b, p, d⟩ ⟨hadmit, x, hx, hne⟩
  have hlen := p.length_add_one_le_of_homogeneousHistory_ne_zero hT i₀
    (hPi hx) (hr b) hne (hbound b p d hadmit ⟨x, hx, hne⟩)
  rw [Nat.mul_add, Nat.mul_one] at hlen
  refine ⟨?_, x, hx, hne⟩
  dsimp only
  omega

end Mei
