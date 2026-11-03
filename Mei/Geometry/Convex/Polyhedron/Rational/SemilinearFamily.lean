/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.LocallyClosed

/-!
# Finite semilinear families and finite branches

A finite semilinear family is a finite collection of charts. Each chart has a rational
semilinear domain in a real vector space `V` with an integral lattice and an evaluation map
to a real vector space `W` with its own integral lattice. The evaluation is piecewise
affine: finitely many rational semilinear pieces cover the domain, and on each piece the
evaluation is an affine map whose linear part is rational. Charts need not be proper and
fibers need not be finite. The fiber over a point of `W` records the chart together with
the preimage point, so overlapping images in different charts are not identified.

The evaluation of a chart is a map on its domain, so families with the same domains and the same
values are equal. A family consists of finite branches when on every chart the domain is a finite
union of locally closed rational-normal polyhedra, and the evaluation restricts to an injective
affine map on each of them. Such domains need not be closed, and a finite branch has finite
fibers.

## Main definitions

* `IsRationalPiecewiseAffine`: a map on a rational semilinear domain that is piecewise affine
  with rational linear parts.
* `IsFiniteBranchOn`: a map on a domain that restricts to affine embeddings, with rational
  linear parts, of finitely many locally closed polyhedra covering the domain.
* `FiniteSemilinearFamily`: finitely many charts with rational piecewise-affine evaluation.
* `FiniteSemilinearFamily.fiber`: the fiber over a point, indexed by chart and preimage.
* `FiniteSemilinearFamily.IsFiniteBranch`: every chart is a finite branch.

## Main results

* `FiniteSemilinearFamily.sum`, `FiniteSemilinearFamily.restrict` and
  `FiniteSemilinearFamily.postcomp`: disjoint union, restriction of the charts to a rational
  semilinear set and post-composition of the evaluation with a rational affine map, with their
  fibers (`fiberSumEquiv`, `fiberRestrictEquiv`, `fiberPostcompEquiv`).
* `FiniteSemilinearFamily.isFiniteBranch_sum_iff`, `FiniteSemilinearFamily.IsFiniteBranch.restrict`:
  finite branches are stable under disjoint union and restriction to rational semilinear sets.
* `FiniteSemilinearFamily.IsFiniteBranch.finite_fiber`: a family of finite branches has finite
  fibers.
* `isFiniteBranchOn_id_Ioo`: the inclusion `(0,1) → ℝ` is a finite branch with a domain that is
  not closed.
* `nat_card_fiber_sum_id`: the disjoint union of two copies of `id : ℝ → ℝ` has fibers of
  cardinality two.
-/

public section

namespace Mei

variable {N V N' W N'' X : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [AddCommGroup W] [Module ℝ W] [AddCommGroup N''] [AddCommGroup X]
  [Module ℝ X] {i : N →+ V} {i' : N' →+ W} {i'' : N'' →+ X}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- A map `f` on `D` is piecewise affine with rational linear parts: finitely many rational
semilinear pieces cover `D`, and on each piece `f` is an affine map, with arbitrary real
offset, whose linear part is rational for the two lattices. -/
def IsRationalPiecewiseAffine (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (D : Set V) (f : D → W) : Prop :=
  ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsRationalSemilinear h (S k) ∧
      Toric.IsRationalLinearMap h h' (g k).linear ∧ ∀ x : D, x.1 ∈ S k → f x = g k x

/-- A map `f` on `D` is a finite branch: finitely many locally closed rational-normal
polyhedra cover `D`, and on each of them `f` agrees with an affine map, with rational
linear part, that is injective on the polyhedron. The domain need not be closed. -/
def IsFiniteBranchOn (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (D : Set V) (f : D → W) : Prop :=
  ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsLocallyClosedPolyhedron h (S k) ∧
      Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.InjOn (g k) (S k) ∧
        ∀ x : D, x.1 ∈ S k → f x = g k x

/-- Unfolds `IsRationalPiecewiseAffine`. -/
theorem isRationalPiecewiseAffine_iff {D : Set V} {f : D → W} :
    IsRationalPiecewiseAffine h h' D f ↔
      ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
        (⋃ k, S k) = D ∧ ∀ k, IsRationalSemilinear h (S k) ∧
          Toric.IsRationalLinearMap h h' (g k).linear ∧ ∀ x : D, x.1 ∈ S k → f x = g k x :=
  Iff.rfl

/-- Unfolds `IsFiniteBranchOn`. -/
theorem isFiniteBranchOn_iff {D : Set V} {f : D → W} :
    IsFiniteBranchOn h h' D f ↔
      ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
        (⋃ k, S k) = D ∧ ∀ k, IsLocallyClosedPolyhedron h (S k) ∧
          Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.InjOn (g k) (S k) ∧
            ∀ x : D, x.1 ∈ S k → f x = g k x :=
  Iff.rfl

namespace IsRationalPiecewiseAffine

/-- The domain of a rational piecewise-affine map is rational semilinear. -/
theorem isRationalSemilinear {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) :
    IsRationalSemilinear h D := by
  obtain ⟨κ, _, S, g, rfl, hS⟩ := hf
  exact IsRationalSemilinear.iUnion fun k => (hS k).1

/-- Restricting to a rational semilinear set keeps the map piecewise affine. -/
theorem inter {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) {P : Set V}
    (hP : IsRationalSemilinear h P) :
    IsRationalPiecewiseAffine h h' (D ∩ P) fun x => f ⟨x.1, x.2.1⟩ := by
  obtain ⟨κ, _, S, g, rfl, hS⟩ := hf
  refine ⟨κ, ‹_›, fun k => S k ∩ P, g, (Set.iUnion_inter ..).symm, fun k =>
    ⟨(hS k).1.inter hP, (hS k).2.1, fun x hx => (hS k).2.2 ⟨x.1, x.2.1⟩ hx.1⟩⟩

/-- Composing the values with a rational affine map keeps the map piecewise affine. -/
theorem postcomp {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear) :
    IsRationalPiecewiseAffine h h'' D fun x => φ (f x) := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  refine ⟨κ, ‹_›, S, fun k => φ.comp (g k), hD, fun k => ⟨(hS k).1, ?_, fun x hx => ?_⟩⟩
  · rw [AffineMap.comp_linear]
    exact hφ.comp (hS k).2.1
  · simp only [AffineMap.comp_apply, (hS k).2.2 x hx]

end IsRationalPiecewiseAffine

namespace IsFiniteBranchOn

/-- A finite branch is piecewise affine with rational linear parts. -/
theorem isRationalPiecewiseAffine {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) :
    IsRationalPiecewiseAffine h h' D f := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  exact ⟨κ, ‹_›, S, g, hD, fun k =>
    ⟨(hS k).1.isRationalSemilinear, (hS k).2.1, (hS k).2.2.2⟩⟩

/-- Restricting a finite branch to a rational semilinear set gives a finite branch. -/
theorem inter {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) {P : Set V}
    (hP : IsRationalSemilinear h P) :
    IsFiniteBranchOn h h' (D ∩ P) fun x => f ⟨x.1, x.2.1⟩ := by
  obtain ⟨κ, _, S, g, rfl, hS⟩ := hf
  obtain ⟨μ, _, C, hC, -, rfl⟩ := isRationalSemilinear_iff_exists_pairwise_disjoint.mp hP
  refine ⟨κ × μ, inferInstance, fun p => S p.1 ∩ C p.2, fun p => g p.1, ?_, fun p =>
    ⟨(hS p.1).1.inter (hC p.2), (hS p.1).2.1, (hS p.1).2.2.1.mono Set.inter_subset_left,
      fun x hx => (hS p.1).2.2.2 ⟨x.1, x.2.1⟩ hx.1⟩⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Prod.exists]
  tauto

/-- A finite branch has finite fibers: on each piece the affine map is injective. -/
theorem finite_fiber {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) (w : W) :
    Finite {x : D // f x = w} := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  have hpiece : ∀ x : D, ∃ k, x.1 ∈ S k := fun x => by
    simpa only [Set.mem_iUnion, ← hD] using x.2
  choose k hk using hpiece
  refine Finite.of_injective (fun x : {x : D // f x = w} => k x.1) fun x y hxy => ?_
  have hxy : k x.1 = k y.1 := hxy
  refine Subtype.ext (Subtype.ext ((hS (k x.1)).2.2.1 (hk x.1) (hxy ▸ hk y.1) ?_))
  rw [← (hS (k x.1)).2.2.2 x.1 (hk x.1), hxy, ← (hS (k y.1)).2.2.2 y.1 (hk y.1)]
  exact x.2.trans y.2.symm

end IsFiniteBranchOn

variable (h h') in
/-- A finite semilinear family: finitely many charts, each with a rational semilinear domain
in `V` and a rational piecewise-affine evaluation map on that domain to `W`. -/
structure FiniteSemilinearFamily (ι : Type*) [Finite ι] where
  /-- The domain of each chart. -/
  domain : ι → Set V
  /-- The evaluation map of each chart, defined on its domain. -/
  eval : ∀ c, domain c → W
  /-- Each chart is piecewise affine with rational linear parts on its domain. -/
  isRationalPiecewiseAffine : ∀ c, IsRationalPiecewiseAffine h h' (domain c) (eval c)

namespace FiniteSemilinearFamily

variable {ι κ : Type*} [Finite ι] [Finite κ] (F : FiniteSemilinearFamily h h' ι)
  (G : FiniteSemilinearFamily h h' κ)

/-- Two families with the same domains and the same values on them are equal. -/
@[ext]
theorem ext {F G : FiniteSemilinearFamily h h' ι} (hd : ∀ c, F.domain c = G.domain c)
    (he : ∀ c (x : V) (hF : x ∈ F.domain c) (hG : x ∈ G.domain c),
      F.eval c ⟨x, hF⟩ = G.eval c ⟨x, hG⟩) : F = G := by
  obtain ⟨d, e, p⟩ := F
  obtain ⟨d', e', p'⟩ := G
  obtain rfl : d = d' := funext hd
  obtain rfl : e = e' := funext fun c => funext fun x => he c x.1 x.2 x.2
  rfl

/-- The fiber of a family over `w`: a chart together with a point of its domain evaluating to
`w`. Points of different charts are never identified. -/
@[expose] def fiber (w : W) : Type _ := Σ c, {x : F.domain c // F.eval c x = w}

/-- A family whose charts are all finite branches. -/
def IsFiniteBranch : Prop := ∀ c, IsFiniteBranchOn h h' (F.domain c) (F.eval c)

/-- Unfolds `IsFiniteBranch`. -/
theorem isFiniteBranch_iff :
    F.IsFiniteBranch ↔ ∀ c, IsFiniteBranchOn h h' (F.domain c) (F.eval c) := Iff.rfl

/-- A family of finite branches has finite fibers. -/
theorem IsFiniteBranch.finite_fiber {F : FiniteSemilinearFamily h h' ι} (hF : F.IsFiniteBranch)
    (w : W) : Finite (F.fiber w) := by
  have := fun c => (hF c).finite_fiber w
  exact inferInstanceAs (Finite (Σ c, {x : F.domain c // F.eval c x = w}))

/-- The family with a single chart. -/
@[expose] def single {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) :
    FiniteSemilinearFamily h h' Unit where
  domain _ := D
  eval _ := f
  isRationalPiecewiseAffine _ := hf

@[simp]
theorem single_domain {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (c : Unit) : (single hf).domain c = D := (rfl)

@[simp]
theorem single_eval {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (c : Unit) : (single hf).eval c = f := (rfl)

/-- A single-chart family consists of finite branches exactly when its chart is a finite
branch. -/
theorem isFiniteBranch_single_iff {D : Set V} {f : D → W}
    (hf : IsRationalPiecewiseAffine h h' D f) :
    (single hf).IsFiniteBranch ↔ IsFiniteBranchOn h h' D f :=
  ⟨fun H => H (), fun H _ => H⟩

/-- The disjoint union of two families, with the charts of both. -/
@[expose] def sum : FiniteSemilinearFamily h h' (ι ⊕ κ) where
  domain := Sum.elim F.domain G.domain
  eval := fun
    | .inl c => F.eval c
    | .inr c => G.eval c
  isRationalPiecewiseAffine := by
    rintro (c | c)
    exacts [F.isRationalPiecewiseAffine c, G.isRationalPiecewiseAffine c]

@[simp]
theorem sum_domain_inl (c : ι) : (F.sum G).domain (.inl c) = F.domain c := (rfl)

@[simp]
theorem sum_domain_inr (c : κ) : (F.sum G).domain (.inr c) = G.domain c := (rfl)

@[simp]
theorem sum_eval_inl (c : ι) : (F.sum G).eval (.inl c) = F.eval c := (rfl)

@[simp]
theorem sum_eval_inr (c : κ) : (F.sum G).eval (.inr c) = G.eval c := (rfl)

/-- The fiber of a disjoint union is the disjoint union of the fibers. -/
def fiberSumEquiv (w : W) : (F.sum G).fiber w ≃ F.fiber w ⊕ G.fiber w :=
  Equiv.sumSigmaDistrib fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w}

/-- Fiber cardinalities add under disjoint union. -/
theorem nat_card_fiber_sum (w : W) [Finite (F.fiber w)] [Finite (G.fiber w)] :
    Nat.card ((F.sum G).fiber w) = Nat.card (F.fiber w) + Nat.card (G.fiber w) := by
  rw [Nat.card_congr (F.fiberSumEquiv G w), Nat.card_sum]

/-- A disjoint union consists of finite branches exactly when both families do. -/
theorem isFiniteBranch_sum_iff :
    (F.sum G).IsFiniteBranch ↔ F.IsFiniteBranch ∧ G.IsFiniteBranch :=
  ⟨fun H => ⟨fun c => H (.inl c), fun c => H (.inr c)⟩, fun H => by
    rintro (c | c)
    exacts [H.1 c, H.2 c]⟩

/-- Restriction of all charts to a rational semilinear set. -/
@[expose] def restrict {P : Set V} (hP : IsRationalSemilinear h P) :
    FiniteSemilinearFamily h h' ι where
  domain c := F.domain c ∩ P
  eval c x := F.eval c ⟨x.1, x.2.1⟩
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).inter hP

@[simp]
theorem restrict_domain {P : Set V} (hP : IsRationalSemilinear h P) (c : ι) :
    (F.restrict hP).domain c = F.domain c ∩ P := (rfl)

@[simp]
theorem restrict_eval {P : Set V} (hP : IsRationalSemilinear h P) (c : ι)
    (x : ↥(F.domain c ∩ P)) : (F.restrict hP).eval c x = F.eval c ⟨x.1, x.2.1⟩ := (rfl)

/-- The fiber of a restriction consists of the points of the original fiber lying in the
restricting set. -/
def fiberRestrictEquiv {P : Set V} (hP : IsRationalSemilinear h P) (w : W) :
    (F.restrict hP).fiber w ≃ {p : F.fiber w // (p.2.1 : V) ∈ P} where
  toFun p := ⟨⟨p.1, ⟨p.2.1.1, p.2.1.2.1⟩, p.2.2⟩, p.2.1.2.2⟩
  invFun p := ⟨p.1.1, ⟨p.1.2.1.1, p.1.2.1.2, p.2⟩, p.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting a family of finite branches to a rational semilinear set gives a family of
finite branches. -/
theorem IsFiniteBranch.restrict {F : FiniteSemilinearFamily h h' ι} {P : Set V}
    (hP : IsRationalSemilinear h P) (hF : F.IsFiniteBranch) :
    (F.restrict hP).IsFiniteBranch :=
  fun c => (hF c).inter hP

/-- Post-composition of the evaluation of all charts with a rational affine map. -/
@[expose] def postcomp (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear) :
    FiniteSemilinearFamily h h'' ι where
  domain := F.domain
  eval c x := φ (F.eval c x)
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).postcomp φ hφ

@[simp]
theorem postcomp_domain (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear) :
    (F.postcomp φ hφ).domain = F.domain := (rfl)

@[simp]
theorem postcomp_eval (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear)
    (c : ι) (x : F.domain c) : (F.postcomp φ hφ).eval c x = φ (F.eval c x) := (rfl)

/-- The fiber of a post-composition over `w'` is the union of the original fibers over the
points of `φ ⁻¹' {w'}`. -/
def fiberPostcompEquiv (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear)
    (w' : X) : (F.postcomp φ hφ).fiber w' ≃ Σ w : {w : W // φ w = w'}, F.fiber w where
  toFun p := ⟨⟨F.eval p.1 p.2.1, p.2.2⟩, p.1, p.2.1, rfl⟩
  invFun p := ⟨p.2.1, p.2.2.1, (congrArg φ p.2.2.2).trans p.1.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨w, hw⟩, c, x, hx⟩
    cases hx
    rfl

end FiniteSemilinearFamily

/-! ### Checks -/

section Checks

variable (h : TauCeti.Toric.IsIntegralLattice (Int.castAddHom ℝ))

/-- The identity of `ℝ` is a rational affine embedding of the whole line. -/
theorem isFiniteBranchOn_id_univ :
    IsFiniteBranchOn h h (Set.univ : Set ℝ) (Subtype.val : ↥(Set.univ : Set ℝ) → ℝ) :=
  ⟨Unit, inferInstance, fun _ => Set.univ, fun _ => AffineMap.id ℝ ℝ, Set.iUnion_const _,
    fun _ => ⟨.univ h, Toric.IsRationalLinearMap.id h, Function.injective_id.injOn,
      fun _ _ => rfl⟩⟩

/-- The inclusion `(0,1) → ℝ` is a finite branch although its domain is not closed. -/
theorem isFiniteBranchOn_id_Ioo :
    IsFiniteBranchOn h h (Set.Ioo 0 1 : Set ℝ) (Subtype.val : ↥(Set.Ioo 0 1 : Set ℝ) → ℝ) := by
  refine ⟨Unit, inferInstance, fun _ => Set.Ioo 0 1, fun _ => AffineMap.id ℝ ℝ,
    Set.iUnion_const _, fun _ => ⟨?_, Toric.IsRationalLinearMap.id h, Function.injective_id.injOn,
      fun _ _ => rfl⟩⟩
  have hid : Toric.IsRationalFunctional h (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    convert Toric.IsRationalFunctional.realCharacter h (LinearMap.id : ℤ →ₗ[ℤ] ℤ) using 1
    exact h.eq_realCharacter (by intro x; simp)
  let r₀ : ℝ →ᴬ[ℝ] ℝ := (-(ContinuousLinearMap.id ℝ ℝ)).toContinuousAffineMap
  let r₁ : ℝ →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap + ContinuousAffineMap.const ℝ ℝ (-1)
  have hr₀ : Toric.IsRationalFunctional h r₀.toAffineMap.linear := by
    have e : r₀.toAffineMap.linear = -LinearMap.id := LinearMap.ext fun x => by
      rw [ContinuousAffineMap.coe_linear_eq_coe_contLinear]
      simp [r₀]
    rw [e]
    exact hid.neg
  have hr₁ : Toric.IsRationalFunctional h r₁.toAffineMap.linear := by
    have e : r₁.toAffineMap.linear = LinearMap.id := LinearMap.ext fun x => by
      rw [ContinuousAffineMap.coe_linear_eq_coe_contLinear]
      simp [r₁]
    rw [e]
    exact hid
  have := isLocallyClosedPolyhedron_setOf_forall_neg (h := h) (κ := Fin 2) ![r₀, r₁]
    (fun k => by fin_cases k <;> assumption)
  have hset : Set.Ioo (0 : ℝ) 1 = {x | ∀ k : Fin 2, (![r₀, r₁] k) x < 0} := by
    ext x
    simp [Fin.forall_fin_two, r₀, r₁]
  rw [hset]
  exact this

/-- The domain `(0,1)` of the inclusion is not closed in `ℝ`. -/
example : ¬ IsClosed (Set.Ioo (0 : ℝ) 1) := by simp

variable {h}

/-- A one-chart family evaluating by the identity on the whole line has a single point in each
fiber. -/
private theorem nat_card_fiber_eq_one {F : FiniteSemilinearFamily h h Unit}
    (hd : F.domain () = Set.univ) (he : ∀ x, F.eval () x = x.1) (w : ℝ) :
    Nat.card (F.fiber w) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨?_⟩, ⟨⟨(), ⟨w, by simp [hd]⟩, by rw [he]⟩⟩⟩
  rintro ⟨⟨⟩, x, hx⟩ ⟨⟨⟩, y, hy⟩
  rw [he] at hx hy
  obtain rfl : x = y := Subtype.ext (hx.trans hy.symm)
  rfl

/-- The disjoint union of two copies of `id : ℝ → ℝ` has fibers of cardinality two: the
coinciding images of the two charts are not identified. -/
theorem nat_card_fiber_sum_id (F G : FiniteSemilinearFamily h h Unit)
    (hFd : F.domain () = Set.univ) (hFe : ∀ x, F.eval () x = x.1)
    (hGd : G.domain () = Set.univ) (hGe : ∀ x, G.eval () x = x.1) (w : ℝ) :
    Nat.card ((F.sum G).fiber w) = 2 := by
  have hF := nat_card_fiber_eq_one hFd hFe w
  have hG := nat_card_fiber_eq_one hGd hGe w
  have := Nat.finite_of_card_ne_zero (hF ▸ one_ne_zero)
  have := Nat.finite_of_card_ne_zero (hG ▸ one_ne_zero)
  rw [F.nat_card_fiber_sum G, hF, hG]

end Checks

end Mei
