/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Refinement
import Mei.Geometry.ScatteringDiagram.DirectedWall.Escape
import Mei.Geometry.Convex.Polyhedron.Path.CentralDifference
import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Uniqueness of outgoing completions

Two consistent subdiagrams of one directed diagram which differ only by outgoing walls
are equivalent. Induct on the order. If they agree at order `k`, then on every
admissible segment their order-`k + 1` transports agree in the central quotient
`G≤k`. The logarithm of the quotient of the two transports is therefore the signed
crossing sum of the differences of the individual wall logarithms, and these differences
vanish on the shared walls. Each homogeneous component of this sum vanishes around
loops by consistency and has nonzero coefficients only on outgoing walls whose ray
carries that degree, so it vanishes along every path by the escape argument.

Consequently two outgoing completions of one family of initial walls are equivalent.
The initial walls need not be full hyperplanes or incoming, and no condition is imposed
on walls whose labels are trivial.

The argument already applies at a single finite cutoff: consistency descends to
the preceding cutoffs by `DirectedDiagram.LevelConsistent.mono`. Thus outgoing
extensions consistent only through order `k` have the same order-`k` products;
their higher-order consistency and inactive added walls are unrestricted.

This is the uniqueness assertion of Travis Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Theorem 2.6,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), and of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
[arXiv:1411.1394v2](https://arxiv.org/abs/1411.1394v2), Appendix C.1. The central
difference is `Quiver.Path.log_wallPathProduct_mul_inv_eq_wallCrossingSum_sub`, and
the escape step is `DirectedWall.wallCrossingSum_eq_zero_of_outgoing`.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement BCHGroup
open scoped symmDiff

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (F : DirectedDiagram (d := d) h H ι)

/-- The active labels of the walls indexed by `s`, and the identity on the other active
walls. -/
private def indicatorLabel (s : Set ι) [DecidablePred (· ∈ s)] (k : ℕ) (j : F.active k) :
    d.truncatedGroup ℒ k :=
  if j.val ∈ s then CompletedGroup.projection k (F.wall j).label else 1

private theorem lie_log_indicatorLabel (s : Set ι) [DecidablePred (· ∈ s)] (k : ℕ)
    (j j' : F.active k)
    (hjj' : affineSpan ℝ (F.wall j).support = affineSpan ℝ (F.wall j').support) :
    ⁅log (F.indicatorLabel s k j), log (F.indicatorLabel s k j')⁆ = 0 := by
  by_cases hj : j.val ∈ s <;> by_cases hj' : j'.val ∈ s <;>
    simp only [indicatorLabel, hj, hj', ↓reduceIte, log_one, zero_lie, lie_zero]
  exact (F.wall j).lie_log_projection_eq_zero_of_direction_eq (F.wall j')
    (congrArg AffineSubspace.direction hjj') k

/-- Products of a restriction are the products of the indicator labels on the original
active walls. -/
private theorem levelPathProduct_restrict_eq (s : Set ι) [DecidablePred (· ∈ s)] (k : ℕ)
    {x y : WallComplement (fun j : F.active k => (F.wall j).support)}
    (r : AdmissiblePLPath x y) :
    (F.restrict s).levelPathProduct k ((F.restrictPathPrefunctor s k).mapPath r) =
      r.wallPathProduct (fun j : F.active k => h.realCharacter (F.wall j).normal)
        (F.indicatorLabel s k) fun j j' hjj' =>
          commute_of_lie_log_eq_zero _ _ (F.lie_log_indicatorLabel s k j j' hjj') :=
  F.levelPathProduct_restrictPathPrefunctor s k _ r

variable {F}

/-- If two subdiagrams agree at order `k`, then the order-`k + 1` transports of their
indicator labels agree in the central quotient of order `k`. -/
private theorem truncation_wallPathProduct_indicatorLabel_eq {s t : Set ι}
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] {k : ℕ}
    (hk : (F.restrict s).LevelEquivalent (F.restrict t) k)
    {x y : WallComplement (fun j : F.active (k + 1) => (F.wall j).support)}
    (r : AdmissiblePLPath x y) :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
        (r.wallPathProduct (fun j : F.active (k + 1) => h.realCharacter (F.wall j).normal)
          (F.indicatorLabel s (k + 1)) fun j j' hjj' =>
            commute_of_lie_log_eq_zero _ _ (F.lie_log_indicatorLabel s (k + 1) j j' hjj')) =
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
        (r.wallPathProduct (fun j : F.active (k + 1) => h.realCharacter (F.wall j).normal)
          (F.indicatorLabel t (k + 1)) fun j j' hjj' =>
            commute_of_lie_log_eq_zero _ _ (F.lie_log_indicatorLabel t (k + 1) j j' hjj')) := by
  let rs := restrictPrefunctor
    (fun j : (F.restrict s).active (k + 1) => ((F.restrict s).wall j).support)
    (Set.inclusion ((F.restrict s).active_mono (Nat.le_succ k)))
  let rt := restrictPrefunctor
    (fun j : (F.restrict t).active (k + 1) => ((F.restrict t).wall j).support)
    (Set.inclusion ((F.restrict t).active_mono (Nat.le_succ k)))
  have hv : (rs.mapPath ((F.restrictPathPrefunctor s (k + 1)).mapPath r)).vertices.map
      WallComplement.val =
        (rt.mapPath ((F.restrictPathPrefunctor t (k + 1)).mapPath r)).vertices.map
          WallComplement.val := by
    rw [vertices_restrictPrefunctor, vertices_restrictPrefunctor,
      vertices_restrictPathPrefunctor, vertices_restrictPathPrefunctor]
  rw [← levelPathProduct_restrict_eq, ← levelPathProduct_restrict_eq,
    truncation_levelPathProduct, truncation_levelPathProduct]
  exact (levelEquivalent_def _ _ k).mp hk _ _ hv

/-- If two consistent subdiagrams differing only by outgoing walls agree at order `k`,
then the indicator labels of their walls have the same order-`k + 1` products. -/
private theorem wallPathProduct_indicatorLabel_eq {s t : Set ι} [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] {k : ℕ}
    (hs : (F.restrict s).LevelConsistent (k + 1)) (ht : (F.restrict t).LevelConsistent (k + 1))
    (hout : ∀ j ∈ F.active (k + 1), j ∈ s ∆ t → (F.wall j).Outgoing)
    (hk : (F.restrict s).LevelEquivalent (F.restrict t) k)
    {x y : WallComplement (fun j : F.active (k + 1) => (F.wall j).support)}
    (r : AdmissiblePLPath x y) :
    r.wallPathProduct (fun j : F.active (k + 1) => h.realCharacter (F.wall j).normal)
        (F.indicatorLabel s (k + 1)) (fun j j' hjj' =>
          commute_of_lie_log_eq_zero _ _ (F.lie_log_indicatorLabel s (k + 1) j j' hjj')) =
      r.wallPathProduct (fun j : F.active (k + 1) => h.realCharacter (F.wall j).normal)
        (F.indicatorLabel t (k + 1)) (fun j j' hjj' =>
          commute_of_lie_log_eq_zero _ _ (F.lie_log_indicatorLabel t (k + 1) j j' hjj')) := by
  classical
  let := h.finiteDimensional
  let ν := fun j : F.active (k + 1) => h.realCharacter (F.wall j).normal
  let a := F.indicatorLabel s (k + 1)
  let b := F.indicatorLabel t (k + 1)
  let c := fun j => log (a j) - log (b j)
  have hdiff {u v : WallComplement (fun j : F.active (k + 1) => (F.wall j).support)}
      (q : AdmissiblePLPath u v) := q.log_wallPathProduct_mul_inv_eq_wallCrossingSum_sub
    (fun j : F.active (k + 1) => (F.wall j).isConvexPolyhedron.isClosed) ν a b
    (F.lie_log_indicatorLabel s (k + 1)) (F.lie_log_indicatorLabel t (k + 1))
    (d.truncationMap ℒ (Nat.le_succ k)) (d.ker_truncationMap_succ_le_center ℒ k)
    fun e => truncation_wallPathProduct_indicatorLabel_eq hk e.toPath
  have hsum : r.wallCrossingSum ν c = 0 := by
    rw [← DirectSum.sum_support_decompose (d.truncatedGrading ℒ (k + 1))
      (r.wallCrossingSum ν c)]
    apply Finset.sum_eq_zero
    intro n _
    let f := ((d.truncatedGrading ℒ (k + 1) n).subtype.comp
      ((DirectSum.component R Γ (fun m => d.truncatedGrading ℒ (k + 1) m) n).comp
        (DirectSum.decomposeLinearEquiv (d.truncatedGrading ℒ (k + 1))).toLinearMap)
      ).toAddMonoidHom
    have hcomp (g : d.completedBCHGroup ℒ) : f (log (CompletedGroup.projection (k + 1) g)) =
        (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
          (log (CompletedGroup.projection (k + 1) g)) n : d.truncatedLie ℒ (k + 1)) :=
      -- `f` is the degree-`n` component map by construction.
      (rfl)
    -- A nonzero coefficient comes from a wall of exactly one subdiagram with `n` on its ray.
    have hwall (j : F.active (k + 1)) (hj : f (c j) ≠ 0) :
        (F.wall j).Outgoing ∧ n ∈ (F.wall j).ray.rayDegrees := by
      have hne : f (log (CompletedGroup.projection (k + 1) (F.wall j).label)) ≠ 0 ∧
          j.val ∈ s ∆ t := by
        by_cases hjs : j.val ∈ s <;> by_cases hjt : j.val ∈ t <;>
          simp_all [c, a, b, indicatorLabel, mem_symmDiff]
      refine ⟨hout j j.property hne.2, ?_⟩
      by_contra hn
      exact hne.1 ((hcomp _).trans
        (H.decompose_log_projection_eq_zero_of_notMem_rayDegrees (F.wall j).label_mem _ hn))
    have hloop (q : AdmissiblePLPath x x) : q.wallCrossingSum ν (fun j => f (c j)) = 0 := by
      have hs' := (levelConsistent_iff_loops _ _).mp hs _
        ((F.restrictPathPrefunctor s (k + 1)).mapPath q)
      have ht' := (levelConsistent_iff_loops _ _).mp ht _
        ((F.restrictPathPrefunctor t (k + 1)).mapPath q)
      rw [levelPathProduct_restrict_eq] at hs' ht'
      rw [← f.map_wallCrossingSum q ν c, ← hdiff q, hs', ht', inv_one, mul_one, log_one,
        map_zero]
    have he := DirectedWall.wallCrossingSum_eq_zero_of_outgoing
      (fun j : F.active (k + 1) => F.wall j) (fun j => f (c j)) hwall hloop r
    rw [← f.map_wallCrossingSum r ν c] at he
    exact he
  rw [← mul_inv_eq_one]
  apply log_injective
  rw [hdiff r, hsum, log_one]

variable (F) in
/-- The first-differing-order step: two subdiagrams of one directed diagram which are
consistent at order `k + 1`, agree at order `k`, and differ only by outgoing walls,
agree at order `k + 1`. Walls in both subdiagrams are unrestricted. -/
theorem levelEquivalent_restrict_succ {s t : Set ι} {k : ℕ}
    (hs : (F.restrict s).LevelConsistent (k + 1)) (ht : (F.restrict t).LevelConsistent (k + 1))
    (hout : ∀ j ∈ F.active (k + 1), j ∈ s ∆ t → (F.wall j).Outgoing)
    (hk : (F.restrict s).LevelEquivalent (F.restrict t) k) :
    (F.restrict s).LevelEquivalent (F.restrict t) (k + 1) := by
  classical
  apply (levelEquivalent_def _ _ _).mpr
  intro x y x' y' p q hpq
  obtain ⟨a, b, r, hP, hQ⟩ := (F.restrict s).exists_common_levelPathProduct_eq
    (F.restrict t) (k + 1) (k + 1)
    (W := fun _ : Unit => fun j : F.active (k + 1) => (F.wall j).support)
    (fun _ j => (F.wall j).isConvexPolyhedron) (fun _ j => (F.wall j).finrank_direction_add_one)
    p q hpq
  let r₀ := (CommonWallComplement.projectionPrefunctor ()).mapPath r
  let r₁ := (F.restrictPathPrefunctor s (k + 1)).mapPath r₀
  let r₂ := (F.restrictPathPrefunctor t (k + 1)).mapPath r₀
  have hv₀ : r₀.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    CommonWallComplement.vertices_projection () r
  have hP' := hP r₁ ((F.vertices_restrictPathPrefunctor s (k + 1) r₀).trans hv₀)
  have hQ' := hQ r₂ ((F.vertices_restrictPathPrefunctor t (k + 1) r₀).trans hv₀)
  rw [← hP', ← hQ', levelPathProduct_restrict_eq, levelPathProduct_restrict_eq]
  exact wallPathProduct_indicatorLabel_eq hs ht hout hk r₀

variable (F) in
/-- Two subdiagrams consistent at order `k` agree at that order if every active
wall belonging to just one of them is outgoing. Consistency at higher orders
is unnecessary. -/
theorem levelEquivalent_restrict_of_outgoing {s t : Set ι} {k : ℕ}
    (hs : (F.restrict s).LevelConsistent k) (ht : (F.restrict t).LevelConsistent k)
    (hout : ∀ j ∈ F.active k, j ∈ s ∆ t → (F.wall j).Outgoing) :
    (F.restrict s).LevelEquivalent (F.restrict t) k := by
  induction k with
  | zero => exact (levelEquivalent_def _ _ 0).mpr fun _ _ _ _ _ _ _ => Subsingleton.elim _ _
  | succ k ih =>
    exact F.levelEquivalent_restrict_succ hs ht hout
      (ih (hs.mono (Nat.le_succ k)) (ht.mono (Nat.le_succ k))
        (fun j hj => hout j (F.active_mono (Nat.le_succ k) hj)))

variable (F) in
/-- Two consistent subdiagrams of one directed diagram which differ only by outgoing walls
are equivalent. Walls with trivial labels need not be outgoing. -/
theorem equivalent_restrict_of_outgoing {s t : Set ι} (hs : (F.restrict s).Consistent)
    (ht : (F.restrict t).Consistent)
    (hout : ∀ j ∈ s ∆ t, (F.wall j).label ≠ 1 → (F.wall j).Outgoing) :
    (F.restrict s).Equivalent (F.restrict t) := by
  exact (equivalent_iff _ _).mpr fun k =>
    F.levelEquivalent_restrict_of_outgoing ((consistent_iff _).mp hs k)
      ((consistent_iff _).mp ht k)
      (fun j hj hst => hout j hst (F.label_ne_one_of_mem_active hj))

section Completion

variable {ι₀ ι' κ : Type*}

/-- An outgoing completion of a family of initial walls: a consistent directed diagram
whose walls indexed by `ι₀` are the initial walls and whose other walls are outgoing. -/
structure IsOutgoingCompletion (D₀ : ι₀ → DirectedWall (d := d) h H)
    (D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')) : Prop where
  /-- The walls indexed by `ι₀` are the initial walls. -/
  wall_inl : ∀ j, D.wall (.inl j) = D₀ j
  /-- Every other wall is outgoing. -/
  outgoing_inr : ∀ j, (D.wall (.inr j)).Outgoing
  /-- The diagram is consistent at every order. -/
  consistent : D.Consistent

/-- The walls of two diagrams on a common initial index set, retaining the initial walls
of the first diagram once. -/
private def union (D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι'))
    (E : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)) :
    DirectedDiagram (d := d) h H (ι₀ ⊕ (ι' ⊕ κ)) where
  wall := Sum.elim (fun j => D.wall (.inl j))
    (Sum.elim (fun j => D.wall (.inr j)) fun j => E.wall (.inr j))
  finite_active k := by
    apply (((D.finite_active k).image (Sum.map id .inl)).union
      ((E.finite_active k).image (Sum.map id .inr))).subset
    rintro (j | j | j) hj
    · exact Or.inl ⟨.inl j, hj, rfl⟩
    · exact Or.inl ⟨.inr j, hj, rfl⟩
    · exact Or.inr ⟨.inr j, hj, rfl⟩

/-- Two diagrams consistent at order `k`, sharing their initial walls and having
only outgoing additional active walls, agree at order `k`. Their labels and
consistency at higher cutoffs are unrestricted. -/
theorem outgoingCompletion_levelEquivalent {k : ℕ}
    {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)}
    (hinitial : ∀ j, D.wall (.inl j) = E.wall (.inl j))
    (hD : D.LevelConsistent k) (hE : E.LevelConsistent k)
    (houtD : ∀ j, Sum.inr j ∈ D.active k → (D.wall (.inr j)).Outgoing)
    (houtE : ∀ j, Sum.inr j ∈ E.active k → (E.wall (.inr j)).Outgoing) :
    D.LevelEquivalent E k := by
  let F := union D E
  let s := range (Sum.map (id : ι₀ → ι₀) (Sum.inl : ι' → ι' ⊕ κ))
  let t := range (Sum.map (id : ι₀ → ι₀) (Sum.inr : κ → ι' ⊕ κ))
  -- Both extensions are reindexings of subdiagrams of the union.
  have hs : (F.restrict s).LevelEquivalent D k := (Refinement.ofEquiv
    (Equiv.ofInjective _ (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩)) (by
      rintro (j | j) <;> rw [restrict_wall, Equiv.ofInjective_apply] <;> rfl)).levelEquivalent k
  have ht : (F.restrict t).LevelEquivalent E k := (Refinement.ofEquiv
    (Equiv.ofInjective _ (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩)) (by
      rintro (j | j) <;> rw [restrict_wall, Equiv.ofInjective_apply]
      · exact (hinitial j).symm
      · rfl)).levelEquivalent k
  refine hs.symm.trans ((F.levelEquivalent_restrict_of_outgoing (hs.symm.consistent hD)
    (ht.symm.consistent hE) ?_).trans ht)
  -- Initial walls are shared, so the two subdiagrams differ only by added walls.
  rintro (j | j | j) hj hst
  · simp [s, t, mem_symmDiff] at hst
  · exact houtD j ((D.mem_active k _).mpr ((F.mem_active k _).mp hj))
  · exact houtE j ((E.mem_active k _).mpr ((F.mem_active k _).mp hj))

/-- Two outgoing completions of the same family of initial walls are equivalent. -/
theorem outgoingCompletion_unique {D₀ : ι₀ → DirectedWall (d := d) h H}
    {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)}
    (hD : IsOutgoingCompletion D₀ D) (hE : IsOutgoingCompletion D₀ E) : D.Equivalent E := by
  exact (equivalent_iff D E).mpr fun k => outgoingCompletion_levelEquivalent
    (fun j => (hD.wall_inl j).trans (hE.wall_inl j).symm)
    ((consistent_iff D).mp hD.consistent k) ((consistent_iff E).mp hE.consistent k)
    (fun j _ => hD.outgoing_inr j) (fun j _ => hE.outgoing_inr j)

end Completion

end Mei.DirectedDiagram
