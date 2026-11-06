/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Image
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification

/-!
# Compatible stratifications of finite branches

Let `F` be a finite semilinear family from `V` to `W`, both with integral lattices, all of whose
charts are finite branches. A *branch stratification* of `F`
(`FiniteSemilinearFamily.BranchStratification`) consists of

* a partition of `W` into nonempty locally closed rational-normal polyhedra, the target strata;
* for each chart, a partition of its domain into locally closed rational-normal polyhedra, the
  source strata, on each of which the evaluation is an affine map with rational linear part
  mapping the source stratum bijectively onto one target stratum.

Thus over each target stratum every source stratum is either absent or an affine copy of it, and
the fiber of `F` over a point of a target stratum `T` is in bijection with the source strata over
`T`; in particular the fiber cardinality is constant on each target stratum
(`FiniteSemilinearFamily.BranchStratification.nat_card_fiber`). The actual bijections
retain chart labels (`BranchStratification.exists_fiberEquiv` and
`BranchStratification.exists_fiberEquiv_of_mem_target`).

Every family of finite branches has a branch stratification
(`FiniteSemilinearFamily.IsFiniteBranch.exists_branchStratification`), so `W` has a finite
partition into nonempty locally closed polyhedra on each of which the fiber cardinality is
constant (`FiniteSemilinearFamily.IsFiniteBranch.exists_partition_nat_card_fiber_eq`). The pieces
of a finite branch may overlap, and a point lying in several pieces of one chart is a single point
of the fiber; every finite branch also has a presentation by pairwise disjoint pieces
(`IsFiniteBranchOn.exists_pairwise_disjoint`).

These are polyhedral analogues of the cell decomposition and uniform finiteness theorems for
definable families in o-minimal geometry (van den Dries, *Tame topology and o-minimal
structures*, Chapter 3). For piecewise-affine families that are not finite branches, a
compatible stratification would need images of polyhedra under non-injective affine maps; it is
not treated here.
-/

public section

open Set

namespace Mei

variable {N V N' W : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W] {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

namespace IsFiniteBranchOn

/-- A finite branch has a presentation by finitely many nonempty, pairwise disjoint locally
closed polyhedra covering its domain, on each of which it agrees with an affine map with rational
linear part that is injective on the polyhedron. -/
theorem exists_pairwise_disjoint {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) :
    ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
      (⋃ k, S k) = D ∧ (Pairwise fun a b => Disjoint (S a) (S b)) ∧ (∀ k, (S k).Nonempty) ∧
        (∀ k, IsLocallyClosedPolyhedron h (S k)) ∧
        (∀ k, Toric.IsRationalLinearMap h h' (g k).linear) ∧ (∀ k, InjOn (g k) (S k)) ∧
        ∀ k (x : D), x.1 ∈ S k → f x = g k x := by
  classical
  obtain ⟨κ, _, S, g, hD, hS⟩ := isFiniteBranchOn_iff.mp hf
  choose hlc hrat hinj heval using hS
  obtain ⟨A, _, C, hC, hdisj, hcover, hmem⟩ := IsRationalSemilinear.exists_common_partition
    (S := S) fun k => (hlc k).isRationalSemilinear
  choose hne hlcC using hC
  -- A cell of the common partition meeting a piece lies in it.
  have hsub {a k x} (hx : x ∈ C a) (hxk : x ∈ S k) : C a ⊆ S k := fun y hy =>
    (hmem a x hx y hy k).mp hxk
  let A' := {a : A // ∃ k, C a ⊆ S k}
  choose k hk using fun a : A' => a.2
  refine ⟨A', inferInstance, fun a => C a, fun a => g (k a), ?_,
    fun a b hab => hdisj (Subtype.coe_injective.ne hab), fun a => hne a, fun a => hlcC a,
    fun a => hrat (k a), fun a => (hinj (k a)).mono (hk a), fun a x hx => heval (k a) x (hk a hx)⟩
  apply Subset.antisymm
  · exact iUnion_subset fun a => (hk a).trans (hD ▸ subset_iUnion S (k a))
  · intro x hx
    obtain ⟨k₀, hx₀⟩ := mem_iUnion.mp (hD ▸ hx)
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨⟨a, k₀, hsub ha hx₀⟩, ha⟩

end IsFiniteBranchOn

namespace FiniteSemilinearFamily

universe u

variable {ι : Type u} [Finite ι] (F : FiniteSemilinearFamily h h' ι)

/-- A branch stratification of a finite semilinear family, with target strata indexed by `κ` and
source strata indexed by `μ`. The target strata partition `W` into nonempty locally closed
polyhedra. The source strata over each chart partition its domain into locally closed polyhedra;
on each of them the evaluation is an affine map with rational linear part that maps it
bijectively onto one target stratum. -/
@[ext]
structure BranchStratification (κ μ : Type*) where
  /-- The target strata. -/
  target : κ → Set W
  /-- The chart containing each source stratum. -/
  chart : μ → ι
  /-- The source strata. -/
  source : μ → Set V
  /-- The target stratum onto which each source stratum is mapped. -/
  stratum : μ → κ
  /-- The target strata are nonempty. -/
  nonempty_target : ∀ b, (target b).Nonempty
  /-- The target strata are locally closed polyhedra. -/
  isLocallyClosedPolyhedron_target : ∀ b, IsLocallyClosedPolyhedron h' (target b)
  /-- Distinct target strata are disjoint. -/
  pairwise_disjoint_target : Pairwise fun b b' => Disjoint (target b) (target b')
  /-- The target strata cover `W`. -/
  iUnion_target : (⋃ b, target b) = univ
  /-- The source strata are locally closed polyhedra. -/
  isLocallyClosedPolyhedron_source : ∀ a, IsLocallyClosedPolyhedron h (source a)
  /-- The source strata of a chart cover its domain. -/
  domain_eq : ∀ c, F.domain c = ⋃ (a) (_ : chart a = c), source a
  /-- Distinct source strata of the same chart are disjoint. -/
  disjoint_source : ∀ a a', chart a = chart a' → a ≠ a' → Disjoint (source a) (source a')
  /-- On each source stratum, the evaluation of its chart agrees with an affine map with rational
  linear part that maps the source stratum bijectively onto its target stratum. -/
  exists_affineMap : ∀ a, ∃ g : V →ᵃ[ℝ] W, Toric.IsRationalLinearMap h h' g.linear ∧
    BijOn g (source a) (target (stratum a)) ∧
      ∀ x : F.domain (chart a), x.1 ∈ source a → F.eval (chart a) x = g x

namespace BranchStratification

variable {F} {κ μ : Type*} (S : F.BranchStratification κ μ)

/-- The source strata are nonempty. -/
theorem nonempty_source (a : μ) : (S.source a).Nonempty := by
  obtain ⟨g, -, hg, -⟩ := S.exists_affineMap a
  exact (hg.image_eq ▸ S.nonempty_target (S.stratum a)).of_image

/-- The evaluation maps each source stratum into its target stratum. -/
theorem eval_mem_target (a : μ) (x : F.domain (S.chart a)) (hx : x.1 ∈ S.source a) :
    F.eval (S.chart a) x ∈ S.target (S.stratum a) := by
  obtain ⟨g, -, hg, heval⟩ := S.exists_affineMap a
  exact heval x hx ▸ hg.mapsTo hx

/-- Over a target stratum, source strata index the actual fiber, retaining the chart
and source stratum of every point. The source and target stratum indices may be infinite. -/
theorem exists_fiberEquiv {b : κ} {w : W} (hw : w ∈ S.target b) :
    ∃ e : {a // S.stratum a = b} ≃ F.fiber w,
      ∀ a, (e a).1 = S.chart a ∧ ((e a).2.1 : V) ∈ S.source a := by
  choose g _ hbij heval using S.exists_affineMap
  -- Each source stratum over `b` has exactly one point over `w`.
  choose x hx hxw using fun a : {a // S.stratum a = b} => (hbij a).surjOn (a.2 ▸ hw)
  have hdom (a : {a // S.stratum a = b}) : x a ∈ F.domain (S.chart a) :=
    S.domain_eq _ ▸ mem_iUnion₂.mpr ⟨a, rfl, hx a⟩
  let e (a : {a // S.stratum a = b}) : F.fiber w :=
    ⟨S.chart a, ⟨x a, hdom a⟩, (heval a ⟨x a, hdom a⟩ (hx a)).trans (hxw a)⟩
  have hbij : Function.Bijective e := by
    refine ⟨fun a a' he => ?_, ?_⟩
    · by_contra hne
      have hxx : x a = x a' := congrArg (fun p : F.fiber w => (p.2.1 : V)) he
      exact (S.disjoint_source a a' (congrArg Sigma.fst he)
        (Subtype.coe_injective.ne hne)).ne_of_mem (hx a) (hxx ▸ hx a') rfl
    · rintro ⟨c, y, hy⟩
      have hy' : (y : V) ∈ ⋃ (a) (_ : S.chart a = c), S.source a := by
        rw [← S.domain_eq c]
        exact y.2
      obtain ⟨a, hac, hya⟩ := mem_iUnion₂.mp hy'
      subst hac
      have hab : S.stratum a = b := by
        by_contra hne
        exact (S.pairwise_disjoint_target hne).ne_of_mem (S.eval_mem_target a y hya) hw hy
      have hxy : x ⟨a, hab⟩ = y :=
        (hbij a).injOn (hx ⟨a, hab⟩) hya ((hxw ⟨a, hab⟩).trans (hy.symm.trans (heval a y hya)))
      exact ⟨⟨a, hab⟩, Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext hxy)))⟩
  exact ⟨Equiv.ofBijective e hbij, fun a => ⟨rfl, hx a⟩⟩

/-- Over a point `w` of the target stratum `b`, the fiber cardinality is the number
of source strata mapped onto `b`. -/
theorem nat_card_fiber {b : κ} {w : W} (hw : w ∈ S.target b) :
    Nat.card (F.fiber w) = Nat.card {a // S.stratum a = b} := by
  obtain ⟨e, -⟩ := S.exists_fiberEquiv hw
  exact (Nat.card_congr e).symm

/-- Two fibers over one target stratum are in bijection, preserving every chart
label. Distinct branches in the same chart are still distinct fiber points. -/
theorem exists_fiberEquiv_of_mem_target {b : κ} {w w' : W}
    (hw : w ∈ S.target b) (hw' : w' ∈ S.target b) :
    ∃ e : F.fiber w ≃ F.fiber w', ∀ x, (e x).1 = x.1 := by
  obtain ⟨e, he⟩ := S.exists_fiberEquiv hw
  obtain ⟨e', he'⟩ := S.exists_fiberEquiv hw'
  refine ⟨e.symm.trans e', fun x => ?_⟩
  exact (he' (e.symm x)).1.trans
    ((he (e.symm x)).1.symm.trans (congrArg Sigma.fst (e.apply_symm_apply x)))

end BranchStratification

namespace IsFiniteBranch

variable {F}

/-- Every family of finite branches has a branch stratification. -/
theorem exists_branchStratification (hF : F.IsFiniteBranch) :
    ∃ (κ : Type) (μ : Type u) (_ : Finite κ) (_ : Finite μ),
      Nonempty (F.BranchStratification κ μ) := by
  classical
  let := h.finiteDimensional
  choose κ hκ S g hD hdisj hne hlc hrat hinj heval using fun c =>
    (F.isFiniteBranch_iff.mp hF c).exists_pairwise_disjoint
  have (c : ι) : Finite (κ c) := hκ c
  -- A common partition of `W` deciding membership in the images of all pieces.
  let Y (p : Σ c, κ c) : Set W := g p.1 p.2 '' S p.1 p.2
  obtain ⟨B, _, T, hT, hTdisj, hTcover, hTmem⟩ := IsRationalSemilinear.exists_common_partition
    (S := Y) fun p =>
      ((hlc p.1 p.2).image_of_injOn _ (hrat p.1 p.2) (hinj p.1 p.2)).isRationalSemilinear
  choose hTne hTlc using hT
  have hsub {b p w} (hw : w ∈ T b) (hwp : w ∈ Y p) : T b ⊆ Y p := fun w' hw' =>
    (hTmem b w hw w' hw' p).mp hwp
  -- A source stratum is the part of a piece mapped into a target stratum inside its image.
  let μ := {q : (Σ c, κ c) × B // T q.2 ⊆ Y q.1}
  let gc (q : μ) : V →ᴬ[ℝ] W := ⟨g q.1.1.1 q.1.1.2, AffineMap.continuous_of_finiteDimensional _⟩
  refine ⟨B, μ, inferInstance, inferInstance, ⟨{
    target := T
    chart := fun q => q.1.1.1
    source := fun q => S q.1.1.1 q.1.1.2 ∩ gc q ⁻¹' T q.1.2
    stratum := fun q => q.1.2
    nonempty_target := hTne
    isLocallyClosedPolyhedron_target := hTlc
    pairwise_disjoint_target := hTdisj
    iUnion_target := hTcover
    isLocallyClosedPolyhedron_source := fun q =>
      (hlc _ _).inter ((hTlc _).preimage (gc q) (hrat _ _))
    domain_eq := fun c => ?_
    disjoint_source := ?_
    exists_affineMap := fun q => ⟨g q.1.1.1 q.1.1.2, hrat _ _,
      ⟨fun x hx => hx.2, (hinj _ _).mono inter_subset_left, fun w hw => ?_⟩,
      fun x hx => heval _ _ x hx.1⟩ }⟩⟩
  · ext x
    rw [← hD c, mem_iUnion]
    refine ⟨fun ⟨k, hk⟩ => ?_, fun hx => ?_⟩
    · obtain ⟨b, hb⟩ := mem_iUnion.mp (hTcover ▸ mem_univ (g c k x))
      exact mem_iUnion₂.mpr ⟨⟨(⟨c, k⟩, b), hsub hb (mem_image_of_mem _ hk)⟩, rfl, hk, hb⟩
    · obtain ⟨q, rfl, hq⟩ := mem_iUnion₂.mp hx
      exact ⟨_, hq.1⟩
  · rintro ⟨⟨⟨c, k⟩, b⟩, hq⟩ ⟨⟨⟨c', k'⟩, b'⟩, hq'⟩ (hc : c = c') hne
    subst hc
    by_cases hk : k = k'
    · subst hk
      exact ((hTdisj fun hb => hne (by subst hb; rfl)).preimage _).mono inter_subset_right
        inter_subset_right
    · exact (hdisj c hk).mono inter_subset_left inter_subset_left
  · obtain ⟨x, hx, rfl⟩ := q.2 hw
    exact ⟨x, ⟨hx, hw⟩, rfl⟩

/-- For a family of finite branches, `W` has a finite partition into nonempty locally closed
polyhedra on each of which the fiber cardinality of the family is constant. -/
theorem exists_partition_nat_card_fiber_eq (hF : F.IsFiniteBranch) :
    ∃ (κ : Type) (_ : Finite κ) (T : κ → Set W),
      (∀ b, (T b).Nonempty ∧ IsLocallyClosedPolyhedron h' (T b)) ∧
        (Pairwise fun b b' => Disjoint (T b) (T b')) ∧ (⋃ b, T b) = univ ∧
          ∀ b, ∀ w ∈ T b, ∀ w' ∈ T b, Nat.card (F.fiber w) = Nat.card (F.fiber w') := by
  obtain ⟨κ, μ, _, _, ⟨S⟩⟩ := hF.exists_branchStratification
  exact ⟨κ, inferInstance, S.target,
    fun b => ⟨S.nonempty_target b, S.isLocallyClosedPolyhedron_target b⟩,
    S.pairwise_disjoint_target, S.iUnion_target,
    fun b w hw w' hw' => (S.nat_card_fiber hw).trans (S.nat_card_fiber hw').symm⟩

end IsFiniteBranch

end FiniteSemilinearFamily

end Mei
