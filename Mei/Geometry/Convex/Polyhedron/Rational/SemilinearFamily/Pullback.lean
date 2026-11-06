/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Equalizer

/-!
# Pullback of finite semilinear families

For a family evaluating in `W` and a rational affine map `φ : X → W`, the pullback
has chart domain consisting of pairs `(v, x)` with `v` in the original chart and
`eval v = φ x`. Evaluation is the second projection. The matching equation is a
rational affine equalizer on each affine piece, so the new domains are semilinear.
No injectivity or surjectivity of `φ` is needed.

The fiber over `x` is canonically the original fiber over `φ x`, with chart indices
and original points retained. Finite branches remain finite branches: on a piece
where the original evaluation is injective, the second projection of the pullback
is injective as well. Identity and successive base changes have canonical domain
equivalences preserving evaluation.
-/

public section

namespace Mei

variable {N N' N'' V W X : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup X]
  [NormedSpace ℝ V] [NormedSpace ℝ W] [NormedSpace ℝ X]
  {i : N →+ V} {i' : N' →+ W} {i'' : N'' →+ X}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}

private theorem iUnion_pullback_pieces {κ : Type*} {D : Set V} {f : D → W}
    (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)) (φ : X →ᵃ[ℝ] W)
    (hD : (⋃ k, S k) = D)
    (hfg : ∀ k (v : D), v.1 ∈ S k → f v = g k v) :
    (⋃ k, Prod.fst ⁻¹' S k ∩ {p : V × X | g k p.1 = φ p.2}) =
      {p : V × X | ∃ hx : p.1 ∈ D, f ⟨p.1, hx⟩ = φ p.2} := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, he⟩
    have hx : p.1 ∈ D := hD ▸ Set.mem_iUnion.mpr ⟨k, hk⟩
    exact ⟨hx, (hfg k ⟨p.1, hx⟩ hk).trans he⟩
  · rintro ⟨hx, he⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hD.symm ▸ hx)
    exact ⟨k, hk, (hfg k ⟨p.1, hx⟩ hk).symm.trans he⟩

private theorem isRationalNormalPolyhedron_pullback_matching (g : V →ᵃ[ℝ] W)
    (φ : X →ᵃ[ℝ] W) (hg : Toric.IsRationalLinearMap h h' g.linear)
    (hφ : Toric.IsRationalLinearMap h'' h' φ.linear) :
    IsRationalNormalPolyhedron (h.prod h'') {p : V × X | g p.1 = φ p.2} :=
  AffineMap.isRationalNormalPolyhedron_equalizer
    (g.comp (AffineMap.fst : V × X →ᵃ[ℝ] V))
    (φ.comp (AffineMap.snd : V × X →ᵃ[ℝ] X))
    (hg.comp (Toric.IsRationalLinearMap.fst h h''))
    (hφ.comp (Toric.IsRationalLinearMap.snd h h''))

/-- The pullback of a piecewise-affine map has rational semilinear domain and
rational affine evaluation, given by the second projection. -/
theorem IsRationalPiecewiseAffine.pullback {D : Set V} {f : D → W}
    (hf : IsRationalPiecewiseAffine h h' D f) (φ : X →ᵃ[ℝ] W)
    (hφ : Toric.IsRationalLinearMap h'' h' φ.linear) :
    IsRationalPiecewiseAffine (h.prod h'') h''
      {p : V × X | ∃ hx : p.1 ∈ D, f ⟨p.1, hx⟩ = φ p.2} (fun p => p.1.2) := by
  let π : V × X →ᴬ[ℝ] V := (ContinuousLinearMap.fst ℝ V X).toContinuousAffineMap
  have hπ : ⇑π = Prod.fst := by
    simp [π, ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.coe_fst']
  obtain ⟨κ, _, S, g, hD, hS⟩ := isRationalPiecewiseAffine_iff.mp hf
  have hpieces (k : κ) : IsRationalSemilinear (h.prod h'')
      (Prod.fst ⁻¹' S k ∩ {p | g k p.1 = φ p.2}) := by
    have heq := isRationalNormalPolyhedron_pullback_matching (g k) φ (hS k).2.1 hφ
    simpa only [hπ] using ((hS k).1.preimage π (Toric.IsRationalLinearMap.fst h h'')).inter
      heq.isLocallyClosedPolyhedron.isRationalSemilinear
  have hdom := iUnion_pullback_pieces S g φ hD (fun k => (hS k).2.2)
  rw [isRationalPiecewiseAffine_iff]
  refine ⟨Unit, inferInstance, fun _ => _, fun _ => AffineMap.snd,
    Set.iUnion_const _, fun _ => ⟨?_, Toric.IsRationalLinearMap.snd h h'', fun _ _ => rfl⟩⟩
  rw [← hdom]
  exact IsRationalSemilinear.iUnion hpieces

/-- Finite branches are preserved by arbitrary rational affine base change.
Only the original evaluation needs to be injective on its pieces. -/
theorem IsFiniteBranchOn.pullback {D : Set V} {f : D → W}
    (hf : IsFiniteBranchOn h h' D f) (φ : X →ᵃ[ℝ] W)
    (hφ : Toric.IsRationalLinearMap h'' h' φ.linear) :
    IsFiniteBranchOn (h.prod h'') h''
      {p : V × X | ∃ hx : p.1 ∈ D, f ⟨p.1, hx⟩ = φ p.2} (fun p => p.1.2) := by
  let π : V × X →ᴬ[ℝ] V := (ContinuousLinearMap.fst ℝ V X).toContinuousAffineMap
  have hπ : ⇑π = Prod.fst := by
    simp [π, ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.coe_fst']
  obtain ⟨κ, _, S, g, hD, hS⟩ := isFiniteBranchOn_iff.mp hf
  rw [isFiniteBranchOn_iff]
  refine ⟨κ, ‹_›, fun k => Prod.fst ⁻¹' S k ∩ {p | g k p.1 = φ p.2},
    fun _ => AffineMap.snd, ?_, fun k => ⟨?_, Toric.IsRationalLinearMap.snd h h'', ?_,
      fun _ _ => rfl⟩⟩
  · exact iUnion_pullback_pieces S g φ hD (fun k => (hS k).2.2.2)
  · have heq := isRationalNormalPolyhedron_pullback_matching (g k) φ (hS k).2.1 hφ
    simpa only [hπ] using ((hS k).1.preimage π (Toric.IsRationalLinearMap.fst h h'')).inter
      heq.isLocallyClosedPolyhedron
  · intro p hp q hq he
    exact Prod.ext ((hS k).2.2.1 hp.1 hq.1 (hp.2.trans ((congrArg φ he).trans hq.2.symm))) he

namespace FiniteSemilinearFamily

variable {ι κ : Type*} [Finite ι] [Finite κ] (F : FiniteSemilinearFamily h h' ι)
  (φ : X →ᵃ[ℝ] W) (hφ : Toric.IsRationalLinearMap h'' h' φ.linear)

/-- Base change of a family along a rational affine target map. The chart index
is unchanged; chart points retain both their original point and their new endpoint. -/
def pullback : FiniteSemilinearFamily (h.prod h'') h'' ι where
  domain c := {p | ∃ hx : p.1 ∈ F.domain c, F.eval c ⟨p.1, hx⟩ = φ p.2}
  eval _ p := p.1.2
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).pullback φ hφ

/-- Membership in a pullback chart is the original domain condition and the
matching equation. -/
@[simp]
theorem mem_pullback_domain (c : ι) (p : V × X) :
    p ∈ (F.pullback φ hφ).domain c ↔
      ∃ hx : p.1 ∈ F.domain c, F.eval c ⟨p.1, hx⟩ = φ p.2 := Iff.rfl

/-- Pullback evaluation is the new endpoint coordinate. -/
@[simp]
theorem pullback_eval (c : ι) (p : (F.pullback φ hφ).domain c) :
    (F.pullback φ hφ).eval c p = p.1.2 := (rfl)

/-- Forgetting the new endpoint sends a pullback chart to its original chart. -/
def pullbackFst (c : ι) (p : (F.pullback φ hφ).domain c) : F.domain c :=
  ⟨p.1.1, p.2.choose⟩

@[simp]
theorem pullbackFst_val (c : ι) (p : (F.pullback φ hφ).domain c) :
    (F.pullbackFst φ hφ c p).1 = p.1.1 := (rfl)

/-- The chart square defining the pullback commutes. -/
@[simp]
theorem eval_pullbackFst (c : ι) (p : (F.pullback φ hφ).domain c) :
    F.eval c (F.pullbackFst φ hφ c p) = φ ((F.pullback φ hφ).eval c p) :=
  p.2.choose_spec

/-- A pair of matching chart points and endpoints determines a pullback point. -/
def pullbackLift (c : ι) (v : F.domain c) (x : X) (hv : F.eval c v = φ x) :
    (F.pullback φ hφ).domain c :=
  ⟨(v.1, x), v.2, hv⟩

@[simp]
theorem pullbackFst_pullbackLift (c : ι) (v : F.domain c) (x : X)
    (hv : F.eval c v = φ x) :
    F.pullbackFst φ hφ c (F.pullbackLift φ hφ c v x hv) = v := (rfl)

@[simp]
theorem pullbackLift_val (c : ι) (v : F.domain c) (x : X)
    (hv : F.eval c v = φ x) :
    (F.pullbackLift φ hφ c v x hv).1 = (v.1, x) := (rfl)

/-- The original point and the new endpoint determine a pullback point uniquely. -/
@[ext]
theorem pullback_ext (c : ι) {p q : (F.pullback φ hφ).domain c}
    (hv : F.pullbackFst φ hφ c p = F.pullbackFst φ hφ c q)
    (hx : (F.pullback φ hφ).eval c p = (F.pullback φ hφ).eval c q) : p = q :=
  Subtype.ext (Prod.ext (congrArg Subtype.val hv) hx)

/-- The fiber after base change is the original fiber over the image endpoint.
Chart indices and original chart points are retained, even for coincident charts. -/
def fiberPullbackEquiv (x : X) : (F.pullback φ hφ).fiber x ≃ F.fiber (φ x) where
  toFun p := ⟨p.1, F.pullbackFst φ hφ p.1 p.2.1,
    (F.eval_pullbackFst φ hφ p.1 p.2.1).trans (congrArg φ p.2.2)⟩
  invFun p := ⟨p.1, F.pullbackLift φ hφ p.1 p.2.1 x p.2.2, rfl⟩
  left_inv p := by
    rcases p with ⟨c, ⟨⟨v, y⟩, hv⟩, he⟩
    cases he
    rfl
  right_inv _ := rfl

@[simp]
theorem fiberPullbackEquiv_apply_fst (x : X) (p : (F.pullback φ hφ).fiber x) :
    (F.fiberPullbackEquiv φ hφ x p).1 = p.1 := (rfl)

@[simp]
theorem fiberPullbackEquiv_apply_snd_val_val (x : X) (p : (F.pullback φ hφ).fiber x) :
    (F.fiberPullbackEquiv φ hφ x p).2.1.1 = p.2.1.1.1 := (rfl)

@[simp]
theorem fiberPullbackEquiv_symm_apply (x : X) (p : F.fiber (φ x)) :
    (F.fiberPullbackEquiv φ hφ x).symm p =
      ⟨p.1, F.pullbackLift φ hφ p.1 p.2.1 x p.2.2, by simp⟩ := (rfl)

/-- Base change preserves fiber cardinality without a finiteness assumption. -/
@[simp]
theorem nat_card_fiber_pullback (x : X) :
    Nat.card ((F.pullback φ hφ).fiber x) = Nat.card (F.fiber (φ x)) :=
  Nat.card_congr (F.fiberPullbackEquiv φ hφ x)

/-- A family of finite branches remains so after rational affine base change. -/
theorem IsFiniteBranch.pullback {F : FiniteSemilinearFamily h h' ι}
    (hF : F.IsFiniteBranch) (φ : X →ᵃ[ℝ] W)
    (hφ : Toric.IsRationalLinearMap h'' h' φ.linear) :
    (F.pullback φ hφ).IsFiniteBranch :=
  (F.pullback φ hφ).isFiniteBranch_iff.mpr fun c =>
    (F.isFiniteBranch_iff.mp hF c).pullback φ hφ

/-- Pullback along the identity has the same chart points as the original family. -/
def pullbackIdEquiv (c : ι) :
    (F.pullback (AffineMap.id ℝ W) (Toric.IsRationalLinearMap.id h')).domain c ≃
      F.domain c where
  toFun := F.pullbackFst _ _ c
  invFun v := F.pullbackLift _ _ c v (F.eval c v) rfl
  left_inv p := F.pullback_ext _ _ c rfl (F.eval_pullbackFst _ _ c p)
  right_inv _ := rfl

@[simp]
theorem pullbackIdEquiv_apply (c : ι)
    (p : (F.pullback (AffineMap.id ℝ W) (Toric.IsRationalLinearMap.id h')).domain c) :
    F.pullbackIdEquiv c p = F.pullbackFst _ _ c p := (rfl)

@[simp]
theorem pullbackIdEquiv_symm_apply (c : ι) (v : F.domain c) :
    (F.pullbackIdEquiv c).symm v = F.pullbackLift _ _ c v (F.eval c v) rfl := (rfl)

variable {N''' Y : Type*} [AddCommGroup N'''] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {i''' : N''' →+ Y} {h''' : TauCeti.Toric.IsIntegralLattice i'''}

/-- Successive base changes agree with base change along the composite, by
forgetting the redundant intermediate endpoint. -/
noncomputable def pullbackCompEquiv (ψ : Y →ᵃ[ℝ] X)
    (hψ : Toric.IsRationalLinearMap h''' h'' ψ.linear)
    (c : ι) :
    ((F.pullback φ hφ).pullback ψ hψ).domain c ≃
      (F.pullback (φ.comp ψ) (hφ.comp hψ)).domain c where
  toFun p := F.pullbackLift _ _ c
    (F.pullbackFst φ hφ c ((F.pullback φ hφ).pullbackFst ψ hψ c p)) p.1.2
    ((F.eval_pullbackFst φ hφ c _).trans
      (congrArg φ ((F.pullback φ hφ).eval_pullbackFst ψ hψ c p)))
  invFun p := (F.pullback φ hφ).pullbackLift ψ hψ c
    (F.pullbackLift φ hφ c (F.pullbackFst _ _ c p) (ψ p.1.2)
      (F.eval_pullbackFst _ _ c p)) p.1.2 rfl
  left_inv p := by
    apply (F.pullback φ hφ).pullback_ext ψ hψ c
    · apply F.pullback_ext φ hφ c
      · rfl
      · exact ((F.pullback φ hφ).eval_pullbackFst ψ hψ c p).symm
    · rfl
  right_inv _ := rfl

@[simp]
theorem pullbackFst_pullbackCompEquiv (ψ : Y →ᵃ[ℝ] X)
    (hψ : Toric.IsRationalLinearMap h''' h'' ψ.linear) (c : ι)
    (p : ((F.pullback φ hφ).pullback ψ hψ).domain c) :
    F.pullbackFst _ _ c (F.pullbackCompEquiv φ hφ ψ hψ c p) =
      F.pullbackFst φ hφ c ((F.pullback φ hφ).pullbackFst ψ hψ c p) := (rfl)

@[simp]
theorem pullbackCompEquiv_symm_apply (ψ : Y →ᵃ[ℝ] X)
    (hψ : Toric.IsRationalLinearMap h''' h'' ψ.linear) (c : ι)
    (p : (F.pullback (φ.comp ψ) (hφ.comp hψ)).domain c) :
    (F.pullbackCompEquiv φ hφ ψ hψ c).symm p =
      (F.pullback φ hφ).pullbackLift ψ hψ c
        (F.pullbackLift φ hφ c (F.pullbackFst _ _ c p) (ψ p.1.2)
          ((F.eval_pullbackFst (φ.comp ψ) (hφ.comp hψ) c p).trans
            (congrArg (fun y => φ (ψ y))
              (F.pullback_eval (φ.comp ψ) (hφ.comp hψ) c p)))) p.1.2
        (by rw [F.pullback_eval φ hφ, F.pullbackLift_val]) := (rfl)

@[simp]
theorem eval_pullbackCompEquiv (ψ : Y →ᵃ[ℝ] X)
    (hψ : Toric.IsRationalLinearMap h''' h'' ψ.linear) (c : ι)
    (p : ((F.pullback φ hφ).pullback ψ hψ).domain c) :
    (F.pullback (φ.comp ψ) (hφ.comp hψ)).eval c (F.pullbackCompEquiv φ hφ ψ hψ c p) =
      ((F.pullback φ hφ).pullback ψ hψ).eval c p := (rfl)

end FiniteSemilinearFamily

/-! The open interval remains a finite branch after constant base change. Duplicating
its chart still gives two points per fiber, even though the matching domains coincide. -/
section Checks

variable (h : TauCeti.Toric.IsIntegralLattice (Int.castAddHom ℝ))

example (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ F : FiniteSemilinearFamily (h.prod h) h (Unit ⊕ Unit),
      F.IsFiniteBranch ∧ (∀ x, Nat.card (F.fiber x) = 2) ∧
        F.domain (.inl ()) = {p : ℝ × ℝ | p.1 = a} := by
  let F := FiniteSemilinearFamily.single (isFiniteBranchOn_id_Ioo h).isRationalPiecewiseAffine
  let φ := AffineMap.const ℝ ℝ a
  have hφ : Toric.IsRationalLinearMap h h φ.linear := by
    rw [Toric.isRationalLinearMap_iff]
    intro ℓ _
    simp [φ]
  have hF : F.IsFiniteBranch :=
    (FiniteSemilinearFamily.isFiniteBranch_single_iff _).mpr (isFiniteBranchOn_id_Ioo h)
  have hcard : ∀ w ∈ Set.Ioo (0 : ℝ) 1, Nat.card (F.fiber w) = 1 := by
    intro w hw
    let e : F.fiber w ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨(), ⟨w, hw⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨⟩, ⟨v, hv⟩, he⟩
          cases he
          rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (by simp)
  refine ⟨(F.sum F).pullback φ hφ,
    (FiniteSemilinearFamily.isFiniteBranch_sum_iff F F).mpr ⟨hF, hF⟩ |>.pullback φ hφ,
    fun x => ?_, ?_⟩
  · have := hF.finite_fiber (φ x)
    rw [FiniteSemilinearFamily.nat_card_fiber_pullback,
      FiniteSemilinearFamily.nat_card_fiber_sum, hcard (φ x) ha]
  · ext p
    simp only [FiniteSemilinearFamily.mem_pullback_domain,
      FiniteSemilinearFamily.sum_domain_inl, FiniteSemilinearFamily.sum_eval_inl,
      Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨he ▸ ha, he⟩⟩

end Checks

end Mei
