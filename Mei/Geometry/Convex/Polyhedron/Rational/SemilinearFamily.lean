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

A family consists of finite branches when on every chart the domain is a finite union of
locally closed rational-normal polyhedra, and the evaluation restricts to an injective
affine map on each of them. Such domains need not be closed.

## Main definitions

* `IsRationalPiecewiseAffine`: a map that is piecewise affine with rational linear parts on a
  rational semilinear domain.
* `IsFiniteBranchOn`: a map that restricts to affine embeddings, with rational linear parts,
  of finitely many locally closed polyhedra covering its domain.
* `FiniteSemilinearFamily`: finitely many charts with rational piecewise-affine evaluation.
* `FiniteSemilinearFamily.fiber`: the fiber over a point, indexed by chart and preimage.
* `FiniteSemilinearFamily.IsFiniteBranch`: every chart is a finite branch.

## Main results

* `FiniteSemilinearFamily.sum`, `FiniteSemilinearFamily.restrict` and
  `FiniteSemilinearFamily.postcomp`: disjoint union, restriction of the charts to a rational
  semilinear set and post-composition of the evaluation with a rational affine map, with their
  fibers (`fiberSumEquiv`, `fiberRestrictEquiv`, `fiberPostcompEquiv`).
* `FiniteSemilinearFamily.isFiniteBranch_sum_iff`, `FiniteSemilinearFamily.IsFiniteBranch.restrict`:
  finite branches are stable under disjoint union and restriction to locally closed polyhedra.
* `isFiniteBranchOn_id_Ioo`, `not_isClosed_Ioo_zero_one`: the inclusion `(0,1) → ℝ` is a finite
  branch with a domain that is not closed.
* `nat_card_fiber_sum_id`: the disjoint union of two copies of `id : ℝ → ℝ` has fibers of
  cardinality two.
* `isIntegralLattice_intCast_real`: the standard lattice `ℤ ⊆ ℝ` used by these checks.
-/

public section

namespace Mei

variable {N V N' W N'' X : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [AddCommGroup W] [Module ℝ W] [AddCommGroup N''] [AddCommGroup X]
  [Module ℝ X] {i : N →+ V} {i' : N' →+ W} {i'' : N'' →+ X}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- A map `f` is piecewise affine with rational linear parts on `D`: finitely many rational
semilinear pieces cover `D`, and on each piece `f` is an affine map, with arbitrary real
offset, whose linear part is rational for the two lattices. -/
def IsRationalPiecewiseAffine (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (f : V → W) (D : Set V) : Prop :=
  ∃ (n : ℕ) (S : Fin n → Set V) (g : Fin n → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsRationalSemilinear h (S k) ∧
      Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.EqOn f (g k) (S k)

/-- A map `f` is a finite branch on `D`: finitely many locally closed rational-normal
polyhedra cover `D`, and on each of them `f` agrees with an affine map, with rational
linear part, that is injective on the polyhedron. The domain need not be closed. -/
def IsFiniteBranchOn (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (f : V → W) (D : Set V) : Prop :=
  ∃ (n : ℕ) (S : Fin n → Set V) (g : Fin n → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsLocallyClosedPolyhedron h (S k) ∧
      Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.InjOn (g k) (S k) ∧
        Set.EqOn f (g k) (S k)

/-- Unfolds `IsRationalPiecewiseAffine`. -/
theorem isRationalPiecewiseAffine_iff {f : V → W} {D : Set V} :
    IsRationalPiecewiseAffine h h' f D ↔
      ∃ (n : ℕ) (S : Fin n → Set V) (g : Fin n → (V →ᵃ[ℝ] W)),
        (⋃ k, S k) = D ∧ ∀ k, IsRationalSemilinear h (S k) ∧
          Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.EqOn f (g k) (S k) :=
  Iff.rfl

/-- Unfolds `IsFiniteBranchOn`. -/
theorem isFiniteBranchOn_iff {f : V → W} {D : Set V} :
    IsFiniteBranchOn h h' f D ↔
      ∃ (n : ℕ) (S : Fin n → Set V) (g : Fin n → (V →ᵃ[ℝ] W)),
        (⋃ k, S k) = D ∧ ∀ k, IsLocallyClosedPolyhedron h (S k) ∧
          Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.InjOn (g k) (S k) ∧
            Set.EqOn f (g k) (S k) :=
  Iff.rfl

namespace IsRationalPiecewiseAffine

/-- The domain of a rational piecewise-affine map is rational semilinear. -/
theorem isRationalSemilinear {f : V → W} {D : Set V} (hf : IsRationalPiecewiseAffine h h' f D) :
    IsRationalSemilinear h D := by
  obtain ⟨n, S, g, rfl, hS⟩ := hf
  exact IsRationalSemilinear.iUnion fun k => (hS k).1

/-- Restricting to a rational semilinear set keeps the map piecewise affine. -/
theorem inter {f : V → W} {D P : Set V} (hf : IsRationalPiecewiseAffine h h' f D)
    (hP : IsRationalSemilinear h P) : IsRationalPiecewiseAffine h h' f (D ∩ P) := by
  obtain ⟨n, S, g, rfl, hS⟩ := hf
  refine ⟨n, fun k => S k ∩ P, g, (Set.iUnion_inter ..).symm, fun k => ⟨(hS k).1.inter hP,
    (hS k).2.1, (hS k).2.2.mono Set.inter_subset_left⟩⟩

/-- Composing the values with a rational affine map keeps the map piecewise affine. -/
theorem postcomp {f : V → W} {D : Set V} (hf : IsRationalPiecewiseAffine h h' f D)
    (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear) :
    IsRationalPiecewiseAffine h h'' (φ ∘ f) D := by
  obtain ⟨n, S, g, hD, hS⟩ := hf
  refine ⟨n, S, fun k => φ.comp (g k), hD, fun k => ⟨(hS k).1, ?_, fun x hx => ?_⟩⟩
  · rw [AffineMap.comp_linear]
    exact hφ.comp (hS k).2.1
  · simp only [Function.comp_apply, AffineMap.comp_apply, (hS k).2.2 hx]

end IsRationalPiecewiseAffine

namespace IsFiniteBranchOn

/-- A finite branch is piecewise affine with rational linear parts. -/
theorem isRationalPiecewiseAffine {f : V → W} {D : Set V} (hf : IsFiniteBranchOn h h' f D) :
    IsRationalPiecewiseAffine h h' f D := by
  obtain ⟨n, S, g, hD, hS⟩ := hf
  exact ⟨n, S, g, hD, fun k => ⟨(hS k).1.isRationalSemilinear, (hS k).2.1, (hS k).2.2.2⟩⟩

/-- Restricting a finite branch to a locally closed polyhedron gives a finite branch. -/
theorem inter {f : V → W} {D P : Set V} (hf : IsFiniteBranchOn h h' f D)
    (hP : IsLocallyClosedPolyhedron h P) : IsFiniteBranchOn h h' f (D ∩ P) := by
  obtain ⟨n, S, g, rfl, hS⟩ := hf
  refine ⟨n, fun k => S k ∩ P, g, (Set.iUnion_inter ..).symm, fun k => ⟨(hS k).1.inter hP,
    (hS k).2.1, (hS k).2.2.1.mono Set.inter_subset_left,
    (hS k).2.2.2.mono Set.inter_subset_left⟩⟩

end IsFiniteBranchOn

variable (h h') in
/-- A finite semilinear family: finitely many charts, each with a rational semilinear domain
in `V` and a rational piecewise-affine evaluation map to `W`. -/
structure FiniteSemilinearFamily (ι : Type*) [Finite ι] where
  /-- The domain of each chart. -/
  domain : ι → Set V
  /-- The evaluation map of each chart, meaningful on its domain. -/
  eval : ι → V → W
  /-- Each chart is piecewise affine with rational linear parts on its domain. -/
  isRationalPiecewiseAffine : ∀ c, IsRationalPiecewiseAffine h h' (eval c) (domain c)

namespace FiniteSemilinearFamily

variable {ι κ : Type*} [Finite ι] [Finite κ] (F : FiniteSemilinearFamily h h' ι)
  (G : FiniteSemilinearFamily h h' κ)

/-- The fiber of a family over `w`: a chart together with a point of its domain evaluating to
`w`. Points of different charts are never identified. -/
@[expose] def fiber (w : W) : Type _ := Σ c, {x : V // x ∈ F.domain c ∧ F.eval c x = w}

/-- A family whose charts are all finite branches. -/
def IsFiniteBranch : Prop := ∀ c, IsFiniteBranchOn h h' (F.eval c) (F.domain c)

/-- Unfolds `IsFiniteBranch`. -/
theorem isFiniteBranch_iff :
    F.IsFiniteBranch ↔ ∀ c, IsFiniteBranchOn h h' (F.eval c) (F.domain c) := Iff.rfl

/-- The family with a single chart. -/
def single {f : V → W} {D : Set V} (hf : IsRationalPiecewiseAffine h h' f D) :
    FiniteSemilinearFamily h h' Unit where
  domain _ := D
  eval _ := f
  isRationalPiecewiseAffine _ := hf

@[simp]
theorem single_domain {f : V → W} {D : Set V} (hf : IsRationalPiecewiseAffine h h' f D)
    (c : Unit) : (single hf).domain c = D := (rfl)

@[simp]
theorem single_eval {f : V → W} {D : Set V} (hf : IsRationalPiecewiseAffine h h' f D)
    (c : Unit) : (single hf).eval c = f := (rfl)

/-- A single-chart family consists of finite branches exactly when its chart is a finite
branch. -/
theorem isFiniteBranch_single_iff {f : V → W} {D : Set V}
    (hf : IsRationalPiecewiseAffine h h' f D) :
    (single hf).IsFiniteBranch ↔ IsFiniteBranchOn h h' f D :=
  ⟨fun H => H (), fun H _ => H⟩

/-- The disjoint union of two families, with the charts of both. -/
def sum : FiniteSemilinearFamily h h' (ι ⊕ κ) where
  domain := Sum.elim F.domain G.domain
  eval := Sum.elim F.eval G.eval
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
def fiberSumEquiv (w : W) : (F.sum G).fiber w ≃ F.fiber w ⊕ G.fiber w where
  toFun
    | ⟨.inl c, x⟩ => .inl ⟨c, x⟩
    | ⟨.inr c, x⟩ => .inr ⟨c, x⟩
  invFun
    | .inl ⟨c, x⟩ => ⟨.inl c, x⟩
    | .inr ⟨c, x⟩ => ⟨.inr c, x⟩
  left_inv := by rintro ⟨c | c, x⟩ <;> rfl
  right_inv := by rintro (⟨c, x⟩ | ⟨c, x⟩) <;> rfl

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
def restrict {P : Set V} (hP : IsRationalSemilinear h P) : FiniteSemilinearFamily h h' ι where
  domain c := F.domain c ∩ P
  eval := F.eval
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).inter hP

@[simp]
theorem restrict_domain {P : Set V} (hP : IsRationalSemilinear h P) (c : ι) :
    (F.restrict hP).domain c = F.domain c ∩ P := (rfl)

@[simp]
theorem restrict_eval {P : Set V} (hP : IsRationalSemilinear h P) :
    (F.restrict hP).eval = F.eval := (rfl)

/-- The fiber of a restriction consists of the points of the original fiber lying in the
restricting set. -/
def fiberRestrictEquiv {P : Set V} (hP : IsRationalSemilinear h P) (w : W) :
    (F.restrict hP).fiber w ≃ {p : F.fiber w // p.2.1 ∈ P} where
  toFun p := ⟨⟨p.1, p.2.1, p.2.2.1.1, p.2.2.2⟩, p.2.2.1.2⟩
  invFun p := ⟨p.1.1, p.1.2.1, ⟨p.1.2.2.1, p.2⟩, p.1.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting a family of finite branches to a locally closed polyhedron gives a family of
finite branches. -/
theorem IsFiniteBranch.restrict {F : FiniteSemilinearFamily h h' ι} {P : Set V}
    (hP : IsLocallyClosedPolyhedron h P) (hF : F.IsFiniteBranch) :
    (F.restrict hP.isRationalSemilinear).IsFiniteBranch :=
  fun c => (hF c).inter hP

/-- Post-composition of the evaluation of all charts with a rational affine map. -/
def postcomp (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear) :
    FiniteSemilinearFamily h h'' ι where
  domain := F.domain
  eval c := φ ∘ F.eval c
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).postcomp φ hφ

@[simp]
theorem postcomp_domain (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear) :
    (F.postcomp φ hφ).domain = F.domain := (rfl)

@[simp]
theorem postcomp_eval (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear)
    (c : ι) : (F.postcomp φ hφ).eval c = φ ∘ F.eval c := (rfl)

/-- The fiber of a post-composition over `w'` is the union of the original fibers over the
points of `φ ⁻¹' {w'}`. -/
def fiberPostcompEquiv (φ : W →ᵃ[ℝ] X) (hφ : Toric.IsRationalLinearMap h' h'' φ.linear)
    (w' : X) : (F.postcomp φ hφ).fiber w' ≃ Σ w : {w : W // φ w = w'}, F.fiber w where
  toFun p := ⟨⟨F.eval p.1 p.2.1, p.2.2.2⟩, p.1, p.2.1, p.2.2.1, rfl⟩
  invFun p := ⟨p.2.1, p.2.2.1, p.2.2.2.1, by
    have := p.1.2
    rw [← p.2.2.2.2] at this
    exact this⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨w, hw⟩, c, x, hx, hf⟩
    cases hf
    rfl

end FiniteSemilinearFamily

/-! ### Checks -/

section Checks

/-- The standard lattice `ℤ ⊆ ℝ` is an integral lattice, so the checks below are not
vacuous. -/
theorem isIntegralLattice_intCast_real : TauCeti.Toric.IsIntegralLattice (Int.castAddHom ℝ) :=
  TauCeti.Toric.isIntegralLattice_of_basis (Module.Basis.singleton Unit ℤ)
    (Module.Basis.singleton Unit ℝ) fun _ => by simp

variable (h : TauCeti.Toric.IsIntegralLattice (Int.castAddHom ℝ))

/-- The identity of `ℝ` is a rational affine embedding of the whole line. -/
theorem isFiniteBranchOn_id_univ : IsFiniteBranchOn h h (id : ℝ → ℝ) Set.univ :=
  ⟨1, fun _ => Set.univ, fun _ => AffineMap.id ℝ ℝ, Set.iUnion_const _,
    fun _ => ⟨.univ h, Toric.IsRationalLinearMap.id h, Function.injective_id.injOn,
      fun _ _ => rfl⟩⟩

/-- The inclusion `(0,1) → ℝ` is a finite branch although its domain is not closed. -/
theorem isFiniteBranchOn_id_Ioo : IsFiniteBranchOn h h (id : ℝ → ℝ) (Set.Ioo 0 1) := by
  refine ⟨1, fun _ => Set.Ioo 0 1, fun _ => AffineMap.id ℝ ℝ, Set.iUnion_const _,
    fun _ => ⟨?_, Toric.IsRationalLinearMap.id h, Function.injective_id.injOn, fun _ _ => rfl⟩⟩
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
theorem not_isClosed_Ioo_zero_one : ¬ IsClosed (Set.Ioo (0 : ℝ) 1) := by
  intro hc
  have := hc.closure_eq
  rw [closure_Ioo zero_ne_one] at this
  exact absurd (this ▸ Set.right_mem_Icc.mpr zero_le_one) (by simp)

variable {h}

/-- A one-chart family evaluating by the identity on the whole line has a single point in each
fiber. -/
private theorem nat_card_fiber_eq_one {F : FiniteSemilinearFamily h h Unit}
    (hd : F.domain () = Set.univ) (he : F.eval () = id) (w : ℝ) : Nat.card (F.fiber w) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨?_⟩, ⟨⟨(), w, by simp [hd], by rw [he]; rfl⟩⟩⟩
  rintro ⟨⟨⟩, x, -, hx⟩ ⟨⟨⟩, y, -, hy⟩
  rw [he] at hx hy
  obtain rfl : x = y := hx.trans hy.symm
  rfl

/-- The disjoint union of two copies of `id : ℝ → ℝ` has fibers of cardinality two: the
coinciding images of the two charts are not identified. -/
theorem nat_card_fiber_sum_id (F G : FiniteSemilinearFamily h h Unit)
    (hFd : F.domain () = Set.univ) (hFe : F.eval () = id)
    (hGd : G.domain () = Set.univ) (hGe : G.eval () = id) (w : ℝ) :
    Nat.card ((F.sum G).fiber w) = 2 := by
  have hF := nat_card_fiber_eq_one hFd hFe w
  have hG := nat_card_fiber_eq_one hGd hGe w
  have := Nat.finite_of_card_ne_zero (hF ▸ one_ne_zero)
  have := Nat.finite_of_card_ne_zero (hG ▸ one_ne_zero)
  rw [F.nat_card_fiber_sum G, hF, hG]

end Checks

end Mei
