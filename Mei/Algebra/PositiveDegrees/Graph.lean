/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Map
public import Mei.Algebra.PositiveDegrees.Ray.Basic

/-!
# Positive degrees on graphs

The graph `(f n, n)` of an additive map carries the positive monoid and degree
of its second coordinate. Its cutoffs are exactly the images of the original
cutoffs, even if `f` has a kernel. Inclusion and projection are positive degree
maps with identity cutoff modulus. Supported primitive rays lift without
changing their integer multipliers or their actual allowed degrees.

This uses `AddSubmonoid.map` for the monoid and the character definition of
`TauCeti.IsPrimitive` for primitive graph vectors. One application is the
principal exponent lattice, where the extra coordinate retains degrees in the
radical of a skew form.
-/

public section

namespace Mei.PositiveDegrees

variable {N M : Type*} [AddCommMonoid N] [AddCommMonoid M]
  (d : PositiveDegrees N) (f : N →+ M)

/-- Positive degrees on the graph of an additive map, with degree read from
the second coordinate. No injectivity assumption on the map is needed. -/
def graph : PositiveDegrees (M × N) where
  monoid := d.monoid.map (f.prod (AddMonoidHom.id N))
  degree := d.degree.comp (AddMonoidHom.snd M N)
  degree_pos := by
    rintro _ ⟨n, hn, rfl⟩ hne
    exact d.degree_pos hn (by rintro rfl; exact hne (by simp))
  finite_le k := by
    apply ((d.finite_cutoff k).image (f.prod (AddMonoidHom.id N))).subset
    rintro _ ⟨⟨n, hn, rfl⟩, hk⟩
    exact ⟨n, d.mem_cutoff.mpr ⟨hn, hk⟩, rfl⟩

/-- An allowed graph degree has its first coordinate determined by its second. -/
@[simp]
theorem mem_graph_monoid (m : M) (n : N) :
    (m, n) ∈ (d.graph f).monoid ↔ n ∈ d.monoid ∧ m = f n := by
  constructor
  · rintro ⟨a, ha, h⟩
    have hn : a = n := congrArg Prod.snd h
    subst a
    exact ⟨ha, (congrArg Prod.fst h).symm⟩
  · rintro ⟨hn, rfl⟩
    exact ⟨n, hn, rfl⟩

/-- The graph degree ignores the first coordinate. -/
@[simp]
theorem graph_degree (m : M) (n : N) : (d.graph f).degree (m, n) = d.degree n := (rfl)

/-- Graph cutoffs are exactly images of the original cutoffs. -/
theorem graph_cutoff (k : ℕ) :
    (d.graph f).cutoff k = (fun n => (f n, n)) '' d.cutoff k := by
  ext ⟨m, n⟩
  simp only [mem_cutoff, mem_graph_monoid, graph_degree, Set.mem_image]
  constructor
  · rintro ⟨⟨hn, rfl⟩, hk⟩
    exact ⟨n, ⟨hn, hk⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hk⟩, h⟩
    cases h
    exact ⟨⟨ha, rfl⟩, hk⟩

/-- Inclusion into the graph preserves cutoffs with identity modulus. -/
def graphMap : PositiveDegreeMap d (d.graph f) where
  toAddMonoidHom := f.prod (AddMonoidHom.id N)
  map_mem hn := (mem_graph_monoid d f _ _).mpr ⟨hn, rfl⟩
  map_ne_zero _ hn h := hn (congrArg Prod.snd h)
  modulus := id
  monotone_modulus := monotone_id
  degree_gt _ _ h := h

/-- Graph inclusion retains the original degree in its second coordinate. -/
@[simp]
theorem graphMap_apply (n : N) : d.graphMap f n = (f n, n) := (rfl)

@[simp]
theorem graphMap_modulus (k : ℕ) : (d.graphMap f).modulus k = k := (rfl)

/-- Projection from the allowed graph degrees preserves cutoffs with identity modulus. -/
def graphProjection : PositiveDegreeMap (d.graph f) d where
  toAddMonoidHom := AddMonoidHom.snd M N
  map_mem hn := ((mem_graph_monoid d f _ _).mp hn).1
  map_ne_zero {n} hn hne h := by
    have hm := ((mem_graph_monoid d f _ _).mp hn).2
    have hzero : n.2 = 0 := h
    exact hne (Prod.ext (by simpa [hzero] using hm) hzero)
  modulus := id
  monotone_modulus := monotone_id
  degree_gt _ _ h := h

@[simp]
theorem graphProjection_apply (x : M × N) : d.graphProjection f x = x.2 := (rfl)

@[simp]
theorem graphProjection_modulus (k : ℕ) : (d.graphProjection f).modulus k = k := (rfl)

/-- Projecting a graph inclusion gives the identity positive degree map. -/
@[simp]
theorem graphProjection_comp_graphMap :
    (d.graphProjection f).comp (d.graphMap f) = PositiveDegreeMap.id d := by
  ext <;> simp

end Mei.PositiveDegrees

namespace Mei.SupportedRay

variable {N M : Type*} [AddCommGroup N] [AddCommGroup M]
  {d : PositiveDegrees N} (w : SupportedRay d) (f : N →+ M)

/-- The graph lift of a supported primitive ray. Its generator remains primitive
because a primitive character can be pulled back along the second projection. -/
def graph : SupportedRay (d.graph f) where
  generator := (f w.generator, w.generator)
  isPrimitive := by
    obtain ⟨χ, hχ⟩ := TauCeti.isPrimitive_def.mp w.isPrimitive
    exact TauCeti.isPrimitive_def.mpr ⟨χ.comp (LinearMap.snd ℤ M N), hχ⟩
  supported := by
    obtain ⟨a, ha, hn⟩ := w.supported
    exact ⟨a, ha, by simpa [map_zsmul] using (d.graphMap f).map_mem hn⟩

@[simp]
theorem graph_generator : (w.graph f).generator = (f w.generator, w.generator) := (rfl)

/-- The actual graph ray degrees are precisely the lifts of the original ray
degrees; a supported primitive generator need not itself be allowed. -/
@[simp]
theorem mem_graph_rayDegrees (m : M) (n : N) :
    (m, n) ∈ (w.graph f).rayDegrees ↔ n ∈ w.rayDegrees ∧ m = f n := by
  simp only [mem_rayDegrees, PositiveDegrees.mem_graph_monoid, graph_generator,
    Prod.smul_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hn, hm⟩, a, ha, _, hna⟩
    exact ⟨⟨hn, a, ha, hna⟩, hm⟩
  · rintro ⟨⟨hn, a, ha, rfl⟩, rfl⟩
    exact ⟨⟨hn, rfl⟩, a, ha, by simp, rfl⟩

end Mei.SupportedRay
