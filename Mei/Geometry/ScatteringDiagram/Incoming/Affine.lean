/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Tail
public import Mei.Geometry.Convex.Recession
public import Mei.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Tactic.Module

/-!
# Incoming affine tails with source coefficients

An incoming source in one affine chart has a degree, a source carrier admitting
its geometric direction in the recession cone, and a linear map from incoming
data to that degree's coefficient module. A tail has that degree's negative
velocity, eventually lies in the carrier, and has nonzero direction and image
coefficient. The zero datum and coefficients killed by the source map admit no tails.

Affine germ rigidity supplies canonical representatives: for a fixed source and
datum, equality of germs is equality of tails. The possible positions at reference
time zero are precisely the affine lines meeting the carrier. Every such position
determines one tail, and each closed half-line restriction is proper.

The carrier need not be convex, closed, nonempty, or rational for these laws.
Rational polyhedra can be supplied as source carriers. These are one-chart source
records and tails before the additional chart, common-facet and deck identifications.
The coefficient modules are arbitrary semiring modules; no bases or finite-rank
hypotheses are imposed. We reuse filter germs, continuous affine maps and recession
cones. The incoming-source setting is that of Gross--Hacking--Siebert, *Theta
functions on varieties with effective anti-canonical class*, §§1 and 3
(arXiv:1601.07081), and Mandel's affine broken lines, Definition 2.10
(arXiv:1503.06183).
-/

public section

namespace Mei

open Set Filter

variable {Γ V R E : Type*} [AddCommMonoid Γ] [AddCommGroup V] [Module ℝ V]
  [Semiring R] [AddCommMonoid E] [Module R E]
  {M : Γ → Type*} [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  {v : Γ →+ V}

/-- One affine source record, with coefficients in its specified degree. -/
structure AffineIncomingSource (R E : Type*) [Semiring R] [AddCommMonoid E] [Module R E]
    (M : Γ → Type*) [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)] (v : Γ →+ V) where
  /-- The developed source carrier. -/
  carrier : Set V
  /-- The incoming degree in this chart. -/
  degree : Γ
  /-- The coefficient supplied by each incoming datum. -/
  coefficient : E →ₗ[R] M degree
  /-- Moving backwards along an incoming tail remains in the source. -/
  direction_mem_recession : v degree ∈ recessionCone carrier

variable [TopologicalSpace V]

/-- An admitted one-chart affine tail, with its unique global affine representative.
The source and incoming datum determine the degree and coefficient; positions
remain in the representative rather than in a discrete type label. -/
structure AffineIncomingTail (S : AffineIncomingSource R E M v) (a : E) where
  /-- The affine representative of the incoming germ. -/
  representative : ℝ →ᴬ[ℝ] V
  /-- The representative has the negative geometric degree as velocity. -/
  velocity : representative.linear 1 = -v S.degree
  /-- The representative is admitted by the source eventually at negative infinity. -/
  eventually_mem : ∀ᶠ t : ℝ in atBot, representative t ∈ S.carrier
  /-- Zero image coefficients do not give incoming tails. -/
  coefficient_ne_zero : S.coefficient a ≠ 0
  /-- Zero spatial velocity belongs to constant sections instead. -/
  direction_ne_zero : v S.degree ≠ 0

namespace AffineIncomingTail

variable {S : AffineIncomingSource R E M v} {a : E}

instance : CoeFun (AffineIncomingTail S a) (fun _ => ℝ → V) :=
  ⟨fun β => β.representative⟩

/-- Tails with the same affine representative agree. -/
@[ext]
theorem ext {β γ : AffineIncomingTail S a}
    (h : β.representative = γ.representative) : β = γ := by
  cases β
  cases γ
  cases h
  rfl

/-- The geometric germ at negative infinity of an admitted tail. -/
def germ (β : AffineIncomingTail S a) : Filter.Germ (atBot : Filter ℝ) V :=
  Filter.Germ.ofFun (fun t => β t)

/-- The geometric germ is represented by the underlying affine path. -/
theorem germ_eq_ofFun (β : AffineIncomingTail S a) :
    β.germ = Filter.Germ.ofFun (fun t => β t) := (rfl)

/-- For a fixed source and datum, its affine germ determines the tail. -/
@[simp]
theorem germ_eq_iff {β γ : AffineIncomingTail S a} : β.germ = γ.germ ↔ β = γ := by
  rw [germ, germ, Filter.Germ.coe_eq]
  constructor
  · intro h
    apply ext
    apply ContinuousAffineMap.toAffineMap_injective
    exact AffineMap.eq_of_eventuallyEq_atBot h
  · rintro rfl
    exact Filter.EventuallyEq.rfl

/-- The affine representative is determined by its position at reference time zero. -/
theorem apply_eq (β : AffineIncomingTail S a) (t : ℝ) :
    β t = β 0 - t • v S.degree := by
  have h := β.representative.toAffineMap.map_vadd (0 : ℝ) t
  have hs : β.representative.linear t = t • β.representative.linear 1 := by
    simpa only [smul_eq_mul, mul_one] using
      β.representative.linear.map_smul t (1 : ℝ)
  calc
    β t = β.representative.linear t + β 0 := by simpa using h
    _ = β 0 - t • v S.degree := by rw [hs, β.velocity]; module

/-- Equal reference positions give equal tails at a fixed source and datum. -/
theorem eq_of_apply_zero_eq {β γ : AffineIncomingTail S a} (h : β 0 = γ 0) : β = γ := by
  apply ext
  ext t
  exact (β.apply_eq t).trans
    ((congrArg (fun Q => Q - t • v S.degree) h).trans (γ.apply_eq t).symm)

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

/-- Restricting a nonzero incoming affine germ to any closed half-line is proper. -/
theorem isProperMap_restrict_Iic (β : AffineIncomingTail S a) (b : ℝ) :
    IsProperMap (fun t : Iic b => β t) := by
  apply β.representative.isProperMap_restrict_Iic
  simpa only [ContinuousAffineMap.coe_contLinear, β.velocity, ne_eq, neg_eq_zero] using
    β.direction_ne_zero

end AffineIncomingTail

namespace AffineIncomingSource

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  (S : AffineIncomingSource R E M v)

/-- The canonical affine line through a position at reference time zero. -/
def line (Q : V) : ℝ →ᴬ[ℝ] V := ContinuousAffineMap.lineMap Q (Q - v S.degree)

/-- The canonical incoming line has the prescribed velocity. -/
@[simp]
theorem line_velocity (Q : V) : (S.line Q).linear 1 = -v S.degree := by
  simp [line, ContinuousAffineMap.lineMap_toAffineMap, AffineMap.lineMap_linear]

/-- Evaluate a canonical incoming representative. -/
@[simp]
theorem line_apply (Q : V) (t : ℝ) : S.line Q t = Q - t • v S.degree := by
  simp only [line, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module']
  module

/-- The allowed reference positions are precisely the lines meeting the source. -/
def endpoints : Set V := {Q | ∃ t : ℝ, S.line Q t ∈ S.carrier}

/-- Membership in the allowed reference positions is intersection with the source. -/
@[simp]
theorem mem_endpoints_iff (Q : V) :
    Q ∈ S.endpoints ↔ ∃ t : ℝ, S.line Q t ∈ S.carrier := Iff.rfl

/-- Source admission is equivalent to a single intersection of the incoming line. -/
theorem line_eventually_mem_iff (Q : V) :
    (∀ᶠ t : ℝ in atBot, S.line Q t ∈ S.carrier) ↔ Q ∈ S.endpoints := by
  apply (S.line Q).toAffineMap.eventually_mem_atBot_iff
  rw [S.line_velocity, neg_neg]
  exact S.direction_mem_recession

/-- A nonzero datum image and a nonzero direction admit exactly the allowed positions. -/
def tailAt {a : E} (ha : S.coefficient a ≠ 0) (hv : v S.degree ≠ 0)
    (Q : S.endpoints) : AffineIncomingTail S a where
  representative := S.line Q
  velocity := S.line_velocity Q
  eventually_mem := (S.line_eventually_mem_iff Q).mpr Q.property
  coefficient_ne_zero := ha
  direction_ne_zero := hv

/-- The admitted tail has its specified reference position. -/
@[simp]
theorem tailAt_apply_zero {a : E} (ha : S.coefficient a ≠ 0) (hv : v S.degree ≠ 0)
    (Q : S.endpoints) : S.tailAt ha hv Q 0 = Q := by
  simp [tailAt]

/-- A tail's reference position satisfies the source admission criterion. -/
theorem mem_endpoints (β : AffineIncomingTail S a) : β 0 ∈ S.endpoints := by
  obtain ⟨t, ht⟩ := β.eventually_mem.exists
  exact ⟨t, by simpa only [line_apply, ← β.apply_eq t] using ht⟩

/-- Incoming tails at a fixed source and datum are classified by their allowed
reference positions; transverse positions are not identified. -/
def endpointEquiv {a : E} (ha : S.coefficient a ≠ 0) (hv : v S.degree ≠ 0) :
    AffineIncomingTail S a ≃ S.endpoints where
  toFun β := ⟨β 0, S.mem_endpoints β⟩
  invFun := S.tailAt ha hv
  left_inv β := AffineIncomingTail.eq_of_apply_zero_eq
    (S.tailAt_apply_zero ha hv ⟨β 0, S.mem_endpoints β⟩)
  right_inv Q := Subtype.ext (S.tailAt_apply_zero ha hv Q)

/-- Classification sends a tail to its reference position with the admission proof. -/
@[simp]
theorem endpointEquiv_apply {a : E} (ha : S.coefficient a ≠ 0) (hv : v S.degree ≠ 0)
    (β : AffineIncomingTail S a) :
    S.endpointEquiv ha hv β = ⟨β 0, S.mem_endpoints β⟩ := (rfl)

/-- Inverse classification constructs the canonical tail at the given reference position. -/
@[simp]
theorem endpointEquiv_symm_apply {a : E} (ha : S.coefficient a ≠ 0)
    (hv : v S.degree ≠ 0) (Q : S.endpoints) :
    (S.endpointEquiv ha hv).symm Q = S.tailAt ha hv Q := (rfl)

/-- A source admits tails precisely when its coefficient image and direction are
nonzero and its carrier is nonempty. In particular zero inputs admit no tails. -/
theorem nonempty_tail_iff (a : E) : Nonempty (AffineIncomingTail S a) ↔
    S.coefficient a ≠ 0 ∧ v S.degree ≠ 0 ∧ S.carrier.Nonempty := by
  constructor
  · rintro ⟨β⟩
    obtain ⟨t, ht⟩ := β.eventually_mem.exists
    exact ⟨β.coefficient_ne_zero, β.direction_ne_zero, β t, ht⟩
  · rintro ⟨ha, hv, Q, hQ⟩
    exact ⟨S.tailAt ha hv ⟨Q, ⟨0, by simpa only [line_apply, zero_smul, sub_zero] using hQ⟩⟩⟩

end AffineIncomingSource

section Chart

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]

namespace AffineIncomingSource

/-- Change affine coordinates, transporting the source carrier and its direction
together. The incoming datum and its coefficient module are unchanged. -/
@[expose]
def mapChart (S : AffineIncomingSource R E M v) (e : V ≃ᴬ[ℝ] W) :
    AffineIncomingSource R E M (e.linear.toLinearMap.toAddMonoidHom.comp v) where
  carrier := e '' S.carrier
  degree := S.degree
  coefficient := S.coefficient
  direction_mem_recession :=
    (e.toAffineEquiv.linear_mem_recessionCone_image S.carrier (v S.degree)).mpr
      S.direction_mem_recession

/-- An affine coordinate change sends the carrier to its image. -/
@[simp]
theorem mapChart_carrier (S : AffineIncomingSource R E M v) (e : V ≃ᴬ[ℝ] W) :
    (S.mapChart e).carrier = e '' S.carrier := (rfl)

/-- Coordinate changes retain the incoming degree label. -/
@[simp]
theorem mapChart_degree (S : AffineIncomingSource R E M v) (e : V ≃ᴬ[ℝ] W) :
    (S.mapChart e).degree = S.degree := (rfl)

/-- Coordinate changes retain the coefficient of each incoming datum. -/
@[simp]
theorem mapChart_coefficient (S : AffineIncomingSource R E M v) (e : V ≃ᴬ[ℝ] W) (a : E) :
    (S.mapChart e).coefficient a = S.coefficient a := (rfl)

end AffineIncomingSource

namespace AffineIncomingTail

variable {S : AffineIncomingSource R E M v} {a : E}

/-- Transport an admitted tail and its source simultaneously through an affine
coordinate change. A translation of coordinates transports its position as well. -/
def mapChart (β : AffineIncomingTail S a) (e : V ≃ᴬ[ℝ] W) :
    AffineIncomingTail (S.mapChart e) a where
  representative := e.toContinuousAffineMap.comp β.representative
  velocity := by
    have hlin : (e.toContinuousAffineMap.comp β.representative).linear 1 =
        e.linear (β.representative.linear 1) := rfl
    rw [hlin, β.velocity, map_neg]
    rfl
  eventually_mem := β.eventually_mem.mono fun t ht => ⟨β t, ht, rfl⟩
  coefficient_ne_zero := β.coefficient_ne_zero
  direction_ne_zero := by
    intro h
    exact β.direction_ne_zero (e.linear.injective (h.trans (map_zero e.linear).symm))

/-- The transported path applies the affine coordinate change pointwise. -/
@[simp]
theorem mapChart_apply (β : AffineIncomingTail S a) (e : V ≃ᴬ[ℝ] W) (t : ℝ) :
    β.mapChart e t = e (β t) := (rfl)

/-- Transport of representatives respects eventual agreement. -/
theorem eventuallyEq_mapChart (β γ : AffineIncomingTail S a) (e : V ≃ᴬ[ℝ] W) :
    (fun t => β.mapChart e t) =ᶠ[atBot] (fun t => γ.mapChart e t) ↔
      (fun t => β t) =ᶠ[atBot] (fun t => γ t) := by
  simp only [mapChart_apply, Filter.EventuallyEq, e.injective.eq_iff]

/-- Pull a transported tail back to its original source. -/
def unmapChart {e : V ≃ᴬ[ℝ] W} (γ : AffineIncomingTail (S.mapChart e) a) :
    AffineIncomingTail S a where
  representative := e.symm.toContinuousAffineMap.comp γ.representative
  velocity := by
    -- The linear projection of the bundled composition is its composed linear maps.
    have hlin : (e.symm.toContinuousAffineMap.comp γ.representative).linear 1 =
        e.symm.linear (γ.representative.linear 1) := rfl
    have hinv : e.symm.linear = e.linear.symm := by
      rw [ContinuousAffineEquiv.toAffineEquiv_symm, AffineEquiv.linear_symm]
    rw [hlin, γ.velocity, hinv]
    simp only [AffineIncomingSource.mapChart_degree, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, map_neg,
      LinearEquiv.symm_apply_apply]
  eventually_mem := γ.eventually_mem.mono fun t ht => by
    rcases ht with ⟨x, hx, hxt⟩
    simpa only [ContinuousAffineMap.comp_apply,
      ContinuousAffineEquiv.coe_toContinuousAffineMap, ← hxt, e.symm_apply_apply] using hx
  coefficient_ne_zero := γ.coefficient_ne_zero
  direction_ne_zero := by
    intro h
    apply γ.direction_ne_zero
    simp only [AffineIncomingSource.mapChart_degree, AddMonoidHom.comp_apply, h, map_zero]

/-- Pullback of a transported representative applies the inverse chart pointwise. -/
@[simp]
theorem unmapChart_apply (e : V ≃ᴬ[ℝ] W)
    (γ : AffineIncomingTail (S.mapChart e) a) (t : ℝ) :
    γ.unmapChart t = e.symm (γ t) := (rfl)

/-- Affine changes of coordinates give equivalences of admitted tails, including
their reference positions. -/
def chartEquiv (e : V ≃ᴬ[ℝ] W) :
    AffineIncomingTail S a ≃ AffineIncomingTail (S.mapChart e) a where
  toFun β := β.mapChart e
  invFun := unmapChart
  left_inv β := by
    apply ext
    ext t
    exact e.symm_apply_apply (β t)
  right_inv γ := by
    apply ext
    ext t
    exact e.apply_symm_apply (γ t)

/-- The chart equivalence transports the entire tail through the affine chart. -/
@[simp]
theorem chartEquiv_apply (e : V ≃ᴬ[ℝ] W) (β : AffineIncomingTail S a) :
    chartEquiv e β = β.mapChart e := (rfl)

/-- The inverse chart equivalence pulls the entire tail back through the inverse chart. -/
@[simp]
theorem chartEquiv_symm_apply (e : V ≃ᴬ[ℝ] W)
    (γ : AffineIncomingTail (S.mapChart e) a) :
    (chartEquiv e).symm γ = γ.unmapChart := (rfl)

end AffineIncomingTail
end Chart

section Regrade

variable {Γ' : Type*} [AddCommMonoid Γ']
  {M' : Γ' → Type*} [∀ p, AddCommMonoid (M' p)] [∀ p, Module R (M' p)]
  (T : Γ →+ Γ') (w : Γ' →+ V) (hw : w.comp T = v)
  (ψ : ∀ p, M p →ₗ[R] M' (T p))

namespace AffineIncomingSource

omit [TopologicalSpace V]

/-- Regrade a source and change its coefficients along a compatible geometric
degree map. The map may have kernels, including on the coefficient module. -/
@[expose]
def regrade (S : AffineIncomingSource R E M v) : AffineIncomingSource R E M' w where
  carrier := S.carrier
  degree := T S.degree
  coefficient := (ψ S.degree).comp S.coefficient
  direction_mem_recession := by
    have hd : w (T S.degree) = v S.degree := DFunLike.congr_fun hw S.degree
    rw [hd]
    exact S.direction_mem_recession

/-- Regrading retains the source carrier. -/
@[simp]
theorem regrade_carrier (S : AffineIncomingSource R E M v) :
    (S.regrade T w hw ψ).carrier = S.carrier := (rfl)

/-- Regrading transports the degree label. -/
@[simp]
theorem regrade_degree (S : AffineIncomingSource R E M v) :
    (S.regrade T w hw ψ).degree = T S.degree := (rfl)

/-- Regrading transports the entire coefficient supplied by an incoming datum. -/
@[simp]
theorem regrade_coefficient (S : AffineIncomingSource R E M v) (a : E) :
    (S.regrade T w hw ψ).coefficient a = ψ S.degree (S.coefficient a) := (rfl)

end AffineIncomingSource

namespace AffineIncomingTail

variable {S : AffineIncomingSource R E M v} {a : E}

/-- Transport a tail when its entire image coefficient survives. Geometry remains
unchanged, including when the degree map is noninjective. -/
def regrade (β : AffineIncomingTail S a) (ha : ψ S.degree (S.coefficient a) ≠ 0) :
    AffineIncomingTail (S.regrade T w hw ψ) a where
  representative := β.representative
  velocity := by
    have hd : w (T S.degree) = v S.degree := DFunLike.congr_fun hw S.degree
    simpa only [AffineIncomingSource.regrade_degree, hd] using β.velocity
  eventually_mem := β.eventually_mem
  coefficient_ne_zero := ha
  direction_ne_zero := by
    have hd : w (T S.degree) = v S.degree := DFunLike.congr_fun hw S.degree
    simpa only [AffineIncomingSource.regrade_degree, hd] using β.direction_ne_zero

/-- Regrading a surviving coefficient retains its entire affine representative. -/
theorem regrade_representative (β : AffineIncomingTail S a)
    (ha : ψ S.degree (S.coefficient a) ≠ 0) :
    (β.regrade T w hw ψ ha).representative = β.representative := (rfl)

/-- Regrading a surviving coefficient retains every point of its representative. -/
@[simp]
theorem regrade_apply (β : AffineIncomingTail S a)
    (ha : ψ S.degree (S.coefficient a) ≠ 0) (t : ℝ) :
    β.regrade T w hw ψ ha t = β t := (rfl)

/-- Coefficient changes and truncation delete precisely the tails with zero image
coefficient, rather than retaining a tail decorated by zero. -/
noncomputable def regrade? (β : AffineIncomingTail S a) :
    Option (AffineIncomingTail (S.regrade T w hw ψ) a) := by
  classical
  exact if h : ψ S.degree (S.coefficient a) = 0 then none else
    some (β.regrade T w hw ψ h)

/-- The deletion criterion is exactly vanishing of the image coefficient. -/
@[simp]
theorem regrade?_eq_none_iff (β : AffineIncomingTail S a) :
    β.regrade? T w hw ψ = none ↔ ψ S.degree (S.coefficient a) = 0 := by
  classical
  simp only [regrade?]
  split_ifs <;> simp_all

/-- Surviving tails have exactly the old affine representative and the transported
coefficient. This specifies the entire output of the partial map. -/
theorem regrade?_eq_some_iff (β : AffineIncomingTail S a)
    (γ : AffineIncomingTail (S.regrade T w hw ψ) a) :
    β.regrade? T w hw ψ = some γ ↔
      ψ S.degree (S.coefficient a) ≠ 0 ∧ γ.representative = β.representative := by
  classical
  by_cases h : ψ S.degree (S.coefficient a) = 0
  · simp [regrade?, h]
  · simp only [regrade?, dite_eq_right h, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨h, rfl⟩
    · rintro ⟨_, hrep⟩
      exact AffineIncomingTail.ext hrep.symm

end AffineIncomingTail
end Regrade
end Mei
