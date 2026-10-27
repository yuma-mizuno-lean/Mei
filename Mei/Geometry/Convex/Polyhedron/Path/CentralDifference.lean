/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product
public import Mei.Geometry.Convex.Polyhedron.Path.Escape
public import Mei.Algebra.Lie.BCH.CentralExtension
import Mei.Geometry.Convex.Polyhedron.Path.LocalCrossing

/-!
# Central differences of wall transports

Two wall label families with the same image in a central BCH quotient differ
by additive central coefficients. The logarithm of the quotient of their path
products is exactly the signed crossing sum of these coefficients. This keeps
every simultaneous indexed crossing and every repeated visit; the original
labels need not commute at different crossing events.

The labels need not agree wall by wall. Suppose instead that the two families agree in
the central quotient on every admissible segment, and that within each family walls with
equal affine spans have labels with commuting logarithms. Then the combined labels of each
simultaneous crossing agree in the quotient, and the logarithm of the quotient of the
transports is the signed crossing sum of the differences of the individual logarithms.
This compares two wall presentations with no common refinement.

After any additive projection, if the surviving coefficients are supported on
walls with compatible normals escaping in a common parallel direction, equality of
the two transports around loops at the initial point forces the projected
difference to vanish along every path from that point. This connects central
differences of transports with the rectangle argument used in outgoing-completion
uniqueness.

The algebra uses `LieHom.log_prod_mul_inv_prod_of_eq` and the flattened
signed-event expansions `Quiver.Path.wallPathProduct_eq_prod_flatMap` and
`Quiver.Path.wallCrossingSum_eq_sum_flatMap`. Single crossing events are isolated by
`WallComplement.exists_segmentCrossingEvents_eq_singleton`. The escape step uses
`Quiver.Path.wallCrossingSum_eq_zero_of_notMem_recessionCone`. The application is
the uniqueness assertion in Travis Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Theorem 2.6,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5).
-/

public section

noncomputable section

open Mei Mei.Convex WallComplement BCHGroup

namespace Quiver.Path

variable {V ι R L L' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing.IsNilpotent L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing.IsNilpotent L']
  {W : ι → Set V} {x y : WallComplement W}

/-- The central difference of two path products is the signed crossing sum of
the logarithmic label differences. Equality in the quotient is required only
for wall indices actually crossed by the path. -/
theorem log_wallPathProduct_mul_inv_eq_wallCrossingSum (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (a b : ι → BCHGroup L)
    (ha : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (a j) (a k))
    (hb : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (b j) (b k))
    (f : L →ₗ⁅R⁆ L') (hc : f.ker ≤ LieAlgebra.center R L)
    (hab : ∀ S ∈ p.signedCrossingEvents ν, ∀ j ∈ S,
      f.bchGroupMap (a j.1) = f.bchGroupMap (b j.1)) :
    log (p.wallPathProduct ν a ha * (p.wallPathProduct ν b hb)⁻¹) =
      p.wallCrossingSum ν (fun j => log (a j * (b j)⁻¹)) := by
  classical
  let l := (p.signedCrossingEvents ν).reverse.flatMap Finset.toList
  have hl : ∀ j ∈ l, f.bchGroupMap (a j.1) = f.bchGroupMap (b j.1) := by
    intro j hj
    obtain ⟨S, hS, hj⟩ := List.mem_flatMap.mp hj
    exact hab S (List.mem_reverse.mp hS) j (Finset.mem_toList.mp hj)
  rw [wallPathProduct_eq_prod_flatMap ν a ha, wallPathProduct_eq_prod_flatMap ν b hb,
    wallCrossingSum_eq_sum_flatMap, f.log_prod_mul_inv_prod_of_eq hc _ _ _
      (fun j hj => by simp only [map_zpow, hl j hj])]
  exact congrArg List.sum
    (List.map_congr_left fun j hj => f.log_zpow_mul_inv_zpow_of_eq hc _ _ (hl j hj) _)

/-- Projected central differences vanish along all paths from `x` if they vanish
around loops at `x` and every wall with nonzero projected coefficient has a
compatible normal, is parallel to `v`, and has `v` outside its recession cone.
Zero-coefficient walls impose no condition. -/
theorem map_log_wallPathProduct_mul_inv_eq_zero_of_notMem_recessionCone
    [FiniteDimensional ℝ V] {E : Type*} [AddCommGroup E]
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 = Module.finrank ℝ V)
    (ν : ι → V →ₗ[ℝ] ℝ) (a b : ι → BCHGroup L)
    (ha : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (a j) (a k))
    (hb : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (b j) (b k))
    (f : L →ₗ⁅R⁆ L') (hc : f.ker ≤ LieAlgebra.center R L)
    (hab : ∀ j, f.bchGroupMap (a j) = f.bchGroupMap (b j)) (π : L →+ E)
    (hν : ∀ j, π (log (a j * (b j)⁻¹)) ≠ 0 →
      LinearMap.ker (ν j) = (affineSpan ℝ (W j)).direction)
    {v : V} (hpar : ∀ j, π (log (a j * (b j)⁻¹)) ≠ 0 → ν j v = 0)
    (hrec : ∀ j, π (log (a j * (b j)⁻¹)) ≠ 0 → v ∉ Set.recessionCone (W j))
    (hloop : ∀ q : AdmissiblePLPath x x,
      π (log (q.wallPathProduct ν a ha * (q.wallPathProduct ν b hb)⁻¹)) = 0)
    (p : AdmissiblePLPath x y) :
    π (log (p.wallPathProduct ν a ha * (p.wallPathProduct ν b hb)⁻¹)) = 0 := by
  have he {u w : WallComplement W} (q : AdmissiblePLPath u w) :
      π (log (q.wallPathProduct ν a ha * (q.wallPathProduct ν b hb)⁻¹)) =
        q.wallCrossingSum ν (fun j => π (log (a j * (b j)⁻¹))) := by
    rw [q.log_wallPathProduct_mul_inv_eq_wallCrossingSum ν a b ha hb f hc
      (fun _ _ j _ => hab j.1), π.map_wallCrossingSum]
  rw [he]
  exact p.wallCrossingSum_eq_zero_of_notMem_recessionCone hpoly hdim ν _ hν hpar hrec
    (fun q => (he q).symm.trans (hloop q))

/-- Every signed event of a polygonal path is a crossing event of one of its segments. -/
private theorem exists_eq_signedCrossingEvent_of_mem (ν : ι → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) {S : Finset (ι × ℤ)} (hS : S ∈ p.signedCrossingEvents ν) :
    ∃ (u v : WallComplement W) (e : u ⟶ v) (t : ℝ),
      t ∈ orderedCrossingTimes e ∧ signedCrossingEvent ν u v t = S := by
  induction p with
  | nil => simp at hS
  | cons p e ih =>
    rw [signedCrossingEvents_cons] at hS
    rcases List.mem_append.mp hS with hS | hS
    · exact ih hS
    · obtain ⟨t, ht, rfl⟩ := (mem_segmentCrossingEvents ν e S).mp hS
      exact ⟨_, _, e, t, ht, rfl⟩

/-- The logarithm of a simultaneous signed crossing product is the signed sum of the
individual logarithms, when labels of walls with equal affine spans have commuting
logarithms. -/
private theorem log_prod_signedCrossingEvent (ν : ι → V →ₗ[ℝ] ℝ) (a : ι → BCHGroup L)
    (ha : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → ⁅log (a j), log (a k)⁆ = 0)
    {u v : WallComplement W} (e : u ⟶ v) (t : ℝ) :
    log (((signedCrossingEvent ν u v t).toList.map fun j => a j.1 ^ j.2).prod) =
      ∑ j ∈ signedCrossingEvent ν u v t, j.2 • log (a j.1) := by
  classical
  let S := signedCrossingEvent ν u v t
  have hspan {j k : ι × ℤ} (hj : j ∈ S) (hk : k ∈ S) :
      affineSpan ℝ (W j.1) = affineSpan ℝ (W k.1) :=
    affineSpan_eq_of_mem_crossingWalls e
      ((mem_crossingWalls u v t j.1).mpr ((mem_signedCrossingEvent ν u v t j.1 j.2).mp hj).1)
      ((mem_crossingWalls u v t k.1).mpr ((mem_signedCrossingEvent ν u v t k.1 k.2).mp hk).1)
  have hlie : (S : Set (ι × ℤ)).Pairwise fun j k => ⁅j.2 • log (a j.1), k.2 • log (a k.1)⁆ = 0 :=
    fun j hj k hk _ => by
      dsimp only
      rw [zsmul_lie, lie_zsmul, ha _ _ (hspan hj hk), zsmul_zero, zsmul_zero]
  have hexp : (fun j : ι × ℤ => a j.1 ^ j.2) = fun j => exp (j.2 • log (a j.1)) := by
    funext j
    rw [exp_zsmul, exp_log]
  have hcomm := hlie.imp fun _ _ hjk => commute_exp_of_lie_eq_zero _ _ hjk
  rw [hexp, ← (Finset.noncommProd_congr (Finset.toList_toFinset S).symm (fun _ _ => rfl)
    hcomm).trans (Finset.noncommProd_toFinset _ _ _ (Finset.nodup_toList S)),
    ← exp_sum_of_lie_eq_zero S _ hlie, log_exp]

/-- Suppose two label families agree in a central quotient on every admissible segment,
and within each family the labels of walls with equal affine spans have commuting
logarithms. Then the central difference of their path products is the signed crossing
sum of the differences of the individual logarithms. Unlike
`Quiver.Path.log_wallPathProduct_mul_inv_eq_wallCrossingSum`, the labels need not agree
wall by wall: only the combined labels of each simultaneous crossing are compared. -/
theorem log_wallPathProduct_mul_inv_eq_wallCrossingSum_sub [FiniteDimensional ℝ V]
    (hclosed : ∀ j, IsClosed (W j)) (ν : ι → V →ₗ[ℝ] ℝ) (a b : ι → BCHGroup L)
    (ha : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → ⁅log (a j), log (a k)⁆ = 0)
    (hb : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → ⁅log (b j), log (b k)⁆ = 0)
    (f : L →ₗ⁅R⁆ L') (hc : f.ker ≤ LieAlgebra.center R L)
    (hab : ∀ {u v : WallComplement W} (e : u ⟶ v),
      f.bchGroupMap (e.toPath.wallPathProduct ν a
        fun j k hjk => commute_of_lie_log_eq_zero _ _ (ha j k hjk)) =
      f.bchGroupMap (e.toPath.wallPathProduct ν b
        fun j k hjk => commute_of_lie_log_eq_zero _ _ (hb j k hjk)))
    (p : AdmissiblePLPath x y) :
    log (p.wallPathProduct ν a (fun j k hjk => commute_of_lie_log_eq_zero _ _ (ha j k hjk)) *
      (p.wallPathProduct ν b fun j k hjk => commute_of_lie_log_eq_zero _ _ (hb j k hjk))⁻¹) =
        p.wallCrossingSum ν (fun j => log (a j) - log (b j)) := by
  classical
  let A := fun S : Finset (ι × ℤ) => (S.toList.map fun j => a j.1 ^ j.2).prod
  let B := fun S : Finset (ι × ℤ) => (S.toList.map fun j => b j.1 ^ j.2).prod
  -- Each event is realized by a short segment, so the hypothesis compares event products.
  have hAB : ∀ S ∈ (p.signedCrossingEvents ν).reverse,
      f.bchGroupMap (A S) = f.bchGroupMap (B S) := by
    intro S hS
    obtain ⟨u, v, e, t, ht, rfl⟩ :=
      exists_eq_signedCrossingEvent_of_mem ν p (List.mem_reverse.mp hS)
    obtain ⟨u', v', e', he'⟩ := exists_segmentCrossingEvents_eq_singleton hclosed ν e ht
    have hprod (c : ι → BCHGroup L) (hc) :
        e'.toPath.wallPathProduct ν c hc =
          ((signedCrossingEvent ν u v t).toList.map fun j => c j.1 ^ j.2).prod := by
      rw [wallPathProduct_eq_prod_signedCrossingEvents, Quiver.Hom.toPath,
        signedCrossingEvents_cons, signedCrossingEvents_nil, List.nil_append, he']
      simp
    have := hab e'
    rwa [hprod, hprod] at this
  rw [wallPathProduct_eq_prod_signedCrossingEvents, wallPathProduct_eq_prod_signedCrossingEvents,
    f.log_prod_mul_inv_prod_of_eq hc _ A B hAB, wallCrossingSum_def, List.map_reverse,
    List.sum_reverse]
  congr 1
  apply List.map_congr_left
  intro S hS
  obtain ⟨u, v, e, t, -, rfl⟩ := exists_eq_signedCrossingEvent_of_mem ν p hS
  -- The quotient of the two event products is central, hence additive with either factor.
  let S := signedCrossingEvent ν u v t
  have hz : log (A S * (B S)⁻¹) ∈ f.ker := by
    have hker : A S * (B S)⁻¹ ∈ f.bchGroupMap.ker := by
      simpa only [div_eq_mul_inv] using
        (MonoidHom.div_mem_ker_iff f.bchGroupMap).mpr (hAB S (List.mem_reverse.mpr hS))
    simpa only [LieHom.ker_bchGroupMap, LieSubalgebra.mem_bchSubgroup,
      LieIdeal.mem_toLieSubalgebra] using hker
  have hlie : ⁅log (A S * (B S)⁻¹), log (B S)⁆ = 0 := by
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule R L L _).mp (hc hz), neg_zero]
  have hA : log (A S) = log (A S * (B S)⁻¹) + log (B S) := by
    rw [← bch_eq_add_of_lie_eq_zero _ _ hlie, ← log_mul, inv_mul_cancel_right]
  rw [eq_sub_of_add_eq hA.symm, log_prod_signedCrossingEvent ν a ha e t,
    log_prod_signedCrossingEvent ν b hb e t]
  simp only [smul_sub, Finset.sum_sub_distrib]

end Quiver.Path
