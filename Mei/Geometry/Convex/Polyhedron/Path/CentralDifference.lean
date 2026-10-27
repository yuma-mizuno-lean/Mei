/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product
public import Mei.Geometry.Convex.Polyhedron.Path.Escape
public import Mei.Algebra.Lie.BCH.CentralExtension

/-!
# Central differences of wall transports

Two wall label families with the same image in a central BCH quotient differ
by additive central coefficients. The logarithm of the quotient of their path
products is exactly the signed crossing sum of these coefficients. This keeps
every simultaneous indexed crossing and every repeated visit; the original
labels need not commute at different crossing events.

After any additive projection, if the surviving coefficients are supported on
walls escaping in a common parallel direction, equality of the two transports
around loops forces the projected difference to vanish along every path. This
connects central differences of transports with the rectangle argument used in
outgoing-completion uniqueness.

The algebra uses `LieHom.log_prod_mul_inv_prod_of_eq` and the signed-event
expansion `Quiver.Path.wallPathProduct_eq_prod_signedCrossingEvents`. The escape
step uses `Quiver.Path.wallCrossingSum_eq_zero_of_notMem_recessionCone`. The
application is the uniqueness assertion in Travis Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Theorem 2.6,
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
  have hp (label : ι → BCHGroup L)
      (hcomm : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) →
        Commute (label j) (label k)) :
      (l.map (fun j => label j.1 ^ j.2)).prod = p.wallPathProduct ν label hcomm := by
    rw [wallPathProduct_eq_prod_signedCrossingEvents]
    simp [l, List.flatMap_def, List.prod_flatten, Function.comp_def]
  have he := f.log_prod_mul_inv_prod_of_eq hc l
    (fun j => a j.1 ^ j.2) (fun j => b j.1 ^ j.2)
    (fun j hj => by simp only [map_zpow, hl j hj])
  rw [hp a ha, hp b hb] at he
  have hs : (l.map (fun j => log (a j.1 ^ j.2 * (b j.1 ^ j.2)⁻¹))).sum =
      p.wallCrossingSum ν (fun j => log (a j * (b j)⁻¹)) := by
    rw [List.map_congr_left (fun j hj => f.log_zpow_mul_inv_zpow_of_eq hc _ _ (hl j hj) _)]
    simp only [l, List.flatMap_def, List.map_flatten, List.sum_flatten,
      List.map_map, List.map_reverse, List.sum_reverse, Function.comp_def, wallCrossingSum_def]
    congr 1
    apply List.map_congr_left
    intro S _
    rw [← List.sum_toFinset _ (Finset.nodup_toList S)]
    simp
  exact he.trans hs

/-- Projected central differences vanish along all paths if they vanish around
loops and every wall with nonzero projected coefficient escapes in a common
parallel direction. Zero-coefficient walls impose no escape condition. -/
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

end Quiver.Path
