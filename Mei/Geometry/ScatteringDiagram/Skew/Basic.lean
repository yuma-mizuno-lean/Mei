/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Module.RayIndex
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Skew lattice data

A skew lattice datum on a lattice `N` consists of a saturated unfrozen sublattice `N_uf`, a
finite-index sublattice `N°` and a rational skew form `{,}` on `N`, subject to the integrality
conditions `{N_uf, N°} ⊆ ℤ` and `{N, N_uf ∩ N°} ⊆ ℤ`. These are the fixed data of the cluster
scattering diagrams of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1 and Appendix B; the presentation follows Nakanishi, *Cluster algebras and scattering
diagrams, Part III*, §§1–3. A skew datum determines the Lie algebra, Poisson action and
principal realization of its scattering diagrams, and its wall normals are the functionals
`{-, κ(n) n}` constructed here.

Morphisms are integer-linear maps preserving the form and carrying the two sublattices into
their counterparts; skew lattice data on finite free lattices form a category.

For a nonzero vector `n`, the normalization `κ(n)` is the ray index of `N°`
(`AddSubgroup.rayIndex`): the positive rational with `ℝ_{>0} n ∩ N° = ℕ_{>0} κ(n) n`.
By convention `κ(0) = 0`. For `n ∈ N_uf` the vector `κ(n) n`
lies in `N_uf ∩ N°`, so `{-, κ(n) n}` is an integral functional on `N`
(`SkewLatticeDatum.normal`).

## Main declarations

* `Mei.SkewLatticeDatum`: a skew lattice datum.
* `Mei.SkewLatticeDatum.Hom`: morphisms of skew lattice data, with identity and composition.
* `Mei.SkewLatticeDatumCat`: the category of skew lattice data on finite free lattices.
* `Mei.SkewLatticeDatum.exists_int_eq_rayIndex_mul_form`: `{a, κ(n) n}` is an integer for
  `n ∈ N_uf`.
* `Mei.SkewLatticeDatum.normal`: the integral functional `{-, κ(n) n}`.
-/

public section

universe u

namespace Mei

/-- A skew lattice datum on `N`: a saturated unfrozen sublattice `N_uf`, a finite-index
sublattice `N°` and a rational skew form `{,}` with `{N_uf, N°} ⊆ ℤ` and `{N, N_uf ∩ N°} ⊆ ℤ`.
The lattice `N` is intended to be finite free; results needing this assume it separately. -/
@[ext]
structure SkewLatticeDatum (N : Type*) [AddCommGroup N] where
  /-- The unfrozen sublattice `N_uf`. -/
  unfrozen : Submodule ℤ N
  /-- The unfrozen sublattice is saturated: `k • n ∈ N_uf` with `k ≠ 0` forces `n ∈ N_uf`. -/
  unfrozen_saturated : unfrozen.toAddSubmonoid.NSMulSaturated
  /-- The finite-index sublattice `N°`. -/
  sublattice : Submodule ℤ N
  /-- The sublattice `N°` has finite index in `N`. -/
  finiteIndex_sublattice : sublattice.toAddSubgroup.FiniteIndex
  /-- The skew form `{,}`, with rational values. -/
  form : N →ₗ[ℤ] N →ₗ[ℤ] ℚ
  /-- The form is alternating, hence skew-symmetric. -/
  isAlt_form : form.IsAlt
  /-- Integrality on `N_uf × N°`. -/
  integral_unfrozen_sublattice : ∀ a ∈ unfrozen, ∀ b ∈ sublattice, ∃ k : ℤ, form a b = k
  /-- Integrality on `N × (N_uf ∩ N°)`. -/
  integral_unfrozen_inf_sublattice : ∀ a, ∀ b ∈ unfrozen ⊓ sublattice, ∃ k : ℤ, form a b = k

namespace SkewLatticeDatum

variable {N N' N'' N''' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup N''']

section Form

variable (D : SkewLatticeDatum N)

/-- The sublattice `N°` of a skew lattice datum has finite index. -/
instance : D.sublattice.toAddSubgroup.FiniteIndex :=
  D.finiteIndex_sublattice

/-- The skew form vanishes on the diagonal. -/
@[simp]
theorem form_self (n : N) : D.form n n = 0 :=
  D.isAlt_form.self_eq_zero n

/-- The skew form is skew-symmetric. -/
theorem form_swap (a b : N) : D.form b a = -D.form a b :=
  (D.isAlt_form.neg a b).symm

variable (hD : ∀ a b, ∃ k : ℤ, D.form a b = k)

/-- The integer-valued skew character `n ↦ {n,-}`, when the form is integral
on the whole lattice. -/
noncomputable def integralCharacter : N →ₗ[ℤ] Module.Dual ℤ N :=
  D.form.codRestrict₂ (Algebra.linearMap ℤ ℚ) Int.cast_injective (fun a b => by
    obtain ⟨k, hk⟩ := hD a b
    exact ⟨k, hk.symm⟩)

/-- The integral character retains the given rational form. -/
@[simp]
theorem cast_integralCharacter_apply (a b : N) :
    (D.integralCharacter hD a b : ℚ) = D.form a b := by
  unfold integralCharacter
  simpa only [Algebra.linearMap_apply, algebraMap_int_eq, Int.coe_castRingHom] using
    (LinearMap.codRestrict₂_apply D.form (Algebra.linearMap ℤ ℚ)
      Int.cast_injective _ a b)

/-- The integral character is alternating. -/
@[simp]
theorem integralCharacter_self (n : N) : D.integralCharacter hD n n = 0 := by
  apply Int.cast_injective (α := ℚ)
  simp

/-- Skew symmetry of the integral character. -/
theorem integralCharacter_swap (a b : N) :
    D.integralCharacter hD b a = -D.integralCharacter hD a b := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_neg, cast_integralCharacter_apply, cast_integralCharacter_apply, D.form_swap]

/-- A left-separating integral skew form has an injective integral character map. -/
theorem integralCharacter_injective (hnd : D.form.SeparatingLeft) :
    Function.Injective (D.integralCharacter hD) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro n hn
  apply hnd n
  intro a
  rw [← D.cast_integralCharacter_apply hD, hn]
  simp

end Form

/-- A morphism of skew lattice data: an integer-linear map preserving the skew form and
carrying the unfrozen sublattice and the finite-index sublattice into their counterparts. -/
@[ext]
structure Hom (D : SkewLatticeDatum N) (D' : SkewLatticeDatum N') where
  /-- The underlying linear map of lattices. -/
  toLinearMap : N →ₗ[ℤ] N'
  /-- The map preserves the skew form. -/
  form_map : ∀ a b, D'.form (toLinearMap a) (toLinearMap b) = D.form a b
  /-- The map carries `N_uf` into `N'_uf`. -/
  unfrozen_le : D.unfrozen ≤ D'.unfrozen.comap toLinearMap
  /-- The map carries `N°` into `N'°`. -/
  sublattice_le : D.sublattice ≤ D'.sublattice.comap toLinearMap

attribute [simp] Hom.form_map

namespace Hom

variable {D : SkewLatticeDatum N} {D' : SkewLatticeDatum N'} {D'' : SkewLatticeDatum N''}
  {D''' : SkewLatticeDatum N'''}

/-- The identity morphism of a skew lattice datum. -/
def id (D : SkewLatticeDatum N) : Hom D D where
  toLinearMap := LinearMap.id
  form_map _ _ := rfl
  unfrozen_le _ h := h
  sublattice_le _ h := h

/-- The composite of morphisms of skew lattice data, `g` after `f`. -/
def comp (g : Hom D' D'') (f : Hom D D') : Hom D D'' where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  form_map a b := by simp
  unfrozen_le _ h := g.unfrozen_le (f.unfrozen_le h)
  sublattice_le _ h := g.sublattice_le (f.sublattice_le h)

/-- The underlying linear map of the identity morphism is the identity. -/
@[simp]
theorem id_toLinearMap (D : SkewLatticeDatum N) : (id D).toLinearMap = LinearMap.id :=
  (rfl)

/-- The underlying linear map of a composite is the composite of the linear maps. -/
@[simp]
theorem comp_toLinearMap (g : Hom D' D'') (f : Hom D D') :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  (rfl)

/-- The identity is a left unit for composition. -/
@[simp]
theorem id_comp (f : Hom D D') : (id D').comp f = f := by
  ext
  simp

/-- The identity is a right unit for composition. -/
@[simp]
theorem comp_id (f : Hom D D') : f.comp (id D) = f := by
  ext
  simp

/-- Composition of morphisms is associative. -/
theorem comp_assoc (h : Hom D'' D''') (g : Hom D' D'') (f : Hom D D') :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  simp

end Hom

section RayIndex

variable [Module.Free ℤ N] (D : SkewLatticeDatum N)

/-- For an unfrozen vector, `κ(n) n` lies in both defining sublattices. -/
theorem rayVector_mem_unfrozen_inf_sublattice {n : N} (hn : n ∈ D.unfrozen) :
    (D.sublattice.toAddSubgroup.rayVector n : N) ∈ D.unfrozen ⊓ D.sublattice :=
  ⟨D.sublattice.toAddSubgroup.rayVector_mem_of_mem
      (K := D.unfrozen.toAddSubgroup) D.unfrozen_saturated hn,
    (D.sublattice.toAddSubgroup.rayVector n).property⟩

/-- Pairing with the normalized lattice vector multiplies the form by the ray index. -/
theorem form_rayVector (a n : N) :
    D.form a (D.sublattice.toAddSubgroup.rayVector n : N) =
      D.sublattice.toAddSubgroup.rayIndex n * D.form a n := by
  have h := congrArg (D.form a) (D.sublattice.toAddSubgroup.den_rayIndex_zsmul_rayVector n)
  simp only [map_zsmul, zsmul_eq_mul] at h
  rw [← Rat.num_div_den (D.sublattice.toAddSubgroup.rayIndex n)]
  have hden : ((D.sublattice.toAddSubgroup.rayIndex n).den : ℚ) ≠ 0 := by positivity
  field_simp
  simpa [mul_comm] using h

/-- For `n ∈ N_uf` and every `a`, the value `{a, κ(n) n} = κ(n) {a, n}` is an integer, where
`κ` is the ray index of `N°`: the vector `κ(n) n` lies in `N_uf ∩ N°`. -/
theorem exists_int_eq_rayIndex_mul_form {n : N} (hn : n ∈ D.unfrozen) (a : N) :
    ∃ k : ℤ, D.sublattice.toAddSubgroup.rayIndex n * D.form a n = k := by
  rw [← D.form_rayVector]
  exact D.integral_unfrozen_inf_sublattice a _ (D.rayVector_mem_unfrozen_inf_sublattice hn)

/-- The integral functional `{-, κ(n) n}` on `N`, for `n ∈ N_uf`, where `κ` is the ray index
of `N°`. -/
noncomputable def normal (n : N) (hn : n ∈ D.unfrozen) : Module.Dual ℤ N :=
  (LinearEquiv.ofInjective (Algebra.linearMap ℤ ℚ) Int.cast_injective).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (D.sublattice.toAddSubgroup.rayIndex n • D.form.flip n)
      (fun a => by
        obtain ⟨k, hk⟩ := D.exists_int_eq_rayIndex_mul_form hn a
        exact ⟨k, hk.symm⟩)

/-- The value of `{-, κ(n) n}` at `a` is `κ(n) {a, n}`. -/
@[simp]
theorem cast_normal_apply {n : N} (hn : n ∈ D.unfrozen) (a : N) :
    (D.normal n hn a : ℚ) = D.sublattice.toAddSubgroup.rayIndex n * D.form a n := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective (Algebra.linearMap ℤ ℚ) Int.cast_injective).apply_symm_apply _)

/-- The integral normal evaluates to the integer value of the form on `κ(n) n`. -/
theorem normal_apply {n : N} (hn : n ∈ D.unfrozen) (a : N) :
    D.normal n hn a = (D.form a (D.sublattice.toAddSubgroup.rayVector n : N)).num := by
  rw [D.form_rayVector, ← D.cast_normal_apply hn a, Rat.num_intCast]

/-- The integral normal of the zero vector is zero. -/
@[simp]
theorem normal_zero : D.normal 0 D.unfrozen.zero_mem = 0 := by
  ext a
  apply Int.cast_injective (α := ℚ)
  simp

/-- The integral normal commutes with negation of the unfrozen vector. -/
@[simp]
theorem normal_neg {n : N} (hn : n ∈ D.unfrozen) :
    D.normal (-n) (D.unfrozen.neg_mem hn) = -D.normal n hn := by
  ext a
  apply Int.cast_injective (α := ℚ)
  simp

/-- The integral normal depends only on the positive ray of its unfrozen vector. -/
@[simp]
theorem normal_zsmul {d : ℤ} (hd : 0 < d) {n : N} (hn : n ∈ D.unfrozen) :
    D.normal (d • n) (D.unfrozen.smul_mem d hn) = D.normal n hn := by
  ext a
  apply Int.cast_injective (α := ℚ)
  simp only [D.cast_normal_apply, AddSubgroup.rayIndex_zsmul _ hd, map_zsmul,
    zsmul_eq_mul]
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- The functional `{-, κ(n) n}` vanishes on `n`. -/
@[simp]
theorem normal_apply_self {n : N} (hn : n ∈ D.unfrozen) : D.normal n hn n = 0 := by
  apply Int.cast_injective (α := ℚ)
  simp

/-- A nonzero unfrozen degree has nonzero normalized normal when the form
separates its right argument. -/
theorem normal_ne_zero (hnd : D.form.SeparatingRight) {n : N}
    (hn : n ∈ D.unfrozen) (hn0 : n ≠ 0) : D.normal n hn ≠ 0 := by
  intro hz
  apply hn0
  apply hnd n
  intro a
  have he := D.cast_normal_apply hn a
  rw [hz, LinearMap.zero_apply, Int.cast_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left
    (ne_of_gt (D.sublattice.toAddSubgroup.rayIndex_pos hn0))

end RayIndex

end SkewLatticeDatum

/-- A finite free lattice equipped with a skew lattice datum: an object of the category of skew
lattice data. -/
structure SkewLatticeDatumCat : Type (u + 1) where
  /-- Bundle a skew lattice datum on a finite free lattice. -/
  of ::
  /-- The underlying lattice. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [free : Module.Free ℤ carrier]
  [finite : Module.Finite ℤ carrier]
  /-- The skew lattice datum on the lattice. -/
  datum : SkewLatticeDatum carrier

namespace SkewLatticeDatumCat

attribute [instance] addCommGroup free finite

instance : CoeSort SkewLatticeDatumCat.{u} (Type u) :=
  ⟨carrier⟩

open CategoryTheory

/-- Skew lattice data on finite free lattices and their morphisms form a category. -/
instance : Category SkewLatticeDatumCat.{u} where
  Hom X Y := SkewLatticeDatum.Hom X.datum Y.datum
  id X := SkewLatticeDatum.Hom.id X.datum
  comp f g := g.comp f
  id_comp f := SkewLatticeDatum.Hom.comp_id f
  comp_id f := SkewLatticeDatum.Hom.id_comp f
  assoc f g h := (SkewLatticeDatum.Hom.comp_assoc h g f).symm

/-- Morphisms in the category are determined by their underlying linear maps. -/
@[ext]
theorem hom_ext {X Y : SkewLatticeDatumCat.{u}} {f g : X ⟶ Y}
    (h : f.toLinearMap = g.toLinearMap) : f = g :=
  SkewLatticeDatum.Hom.ext h

/-- The underlying linear map of the identity morphism is the identity. -/
@[simp]
theorem id_toLinearMap (X : SkewLatticeDatumCat.{u}) :
    (𝟙 X : X ⟶ X).toLinearMap = LinearMap.id :=
  (rfl)

/-- The underlying linear map of a composite is the composite of the linear maps. -/
@[simp]
theorem comp_toLinearMap {X Y Z : SkewLatticeDatumCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  (rfl)

end SkewLatticeDatumCat

end Mei
