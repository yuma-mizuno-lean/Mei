/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Class
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Relative
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Presentation

/-!
# The relative outgoing scattering class

Let `π : ℒ → ℳ` be a fixed-degree graded Lie homomorphism with a graded Lie section `sec`,
both preserving the directed wall spaces. A *relative input* consists of a consistent
diagram `G` in `ℳ`, the quotient diagram, and a family `W` of full affine hyperplanes in `ℒ`
whose labels are killed by `π`. A *relative outgoing completion* keeps the lift of `G` along
`sec` and the walls `W` fixed and adds only outgoing walls, born at their own degree, with
logarithms in the kernel of `π`.

`exists_isRelativeOutgoingCompletion` packages `exists_relativeOutgoingCompletion`: every
relative input has a relative outgoing completion, whose image under `π` is equivalent to the
quotient diagram. Any two relative outgoing completions of equivalent quotient diagrams and
equivalent ideal inputs are equivalent (`IsRelativeOutgoingCompletion.equivalent_of_equivalent`),
with the finite-order form `projection_relativeScat_eq_of_levelEquivalent`. Hence the
relative scattering class `relativeScat` is well defined, depends only on the equivalence
classes of the quotient diagram and of the ideal input, and commutes with a morphism of split
extensions that preserves the wall spaces (`map_relativeScat`).

The ideal `ker π` is not assumed abelian, and the walls of `W` are arbitrary full hyperplanes
carrying labels in `ker π`. The construction is that of Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Theorem 2.6,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), run over an ideal as in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
[arXiv:1411.1394v2](https://arxiv.org/abs/1411.1394v2), Appendix C.3.
-/

public section

noncomputable section

universe u v w z

namespace Mei.DirectedDiagram

variable {Γ : Type u} {V : Type v} {Λ R : Type*} {L L' : Type w} {ι κ : Type z}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ} {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  (π : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hπ : ∀ n m, ∀ x ∈ H.wall n m, π x ∈ H'.wall n m)
  (sec : GradedLieHom (PositiveDegreeMap.id d) ℳ ℒ)
  (hs : ∀ n m, ∀ x ∈ H'.wall n m, sec x ∈ H.wall n m)
  (G : DirectedDiagram (d := d) h H' ι) (W : DirectedDiagram (d := d) h H κ)

/-- Mapping coefficients commutes with adjoining wall families. -/
theorem map_append {κ' : Type*} (E : DirectedDiagram (d := d) h H κ')
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m) :
    (W.append E).map f hf = (W.map f hf).append (E.map f hf) := by
  apply DirectedDiagram.ext
  funext j
  cases j <;> simp

/-- The data of a relative completion problem: a consistent quotient diagram `G`, and ideal
inputs `W` which are full affine hyperplanes whose labels are killed by `π`. -/
structure IsRelativeCompletionInput : Prop where
  /-- The quotient diagram is consistent at every order. -/
  consistent : G.Consistent
  /-- Every ideal input is a full affine hyperplane. -/
  exists_support_eq_hyperplane : ∀ j, ∃ a : ℝ,
    (W.wall j).support = {v | h.realCharacter (W.wall j).normal v = a}
  /-- The labels of the ideal inputs lie in the kernel of `π`. -/
  completedMap_label_eq_one : ∀ j, π.completedMap (W.wall j).label = 1

/-- `F` is a relative outgoing completion of the quotient diagram `G` and the ideal inputs `W`:
it retains the lift of `G` along `sec` and the walls `W`, is consistent, and adds only outgoing
walls with a pure birth logarithm in the kernel of `π`. -/
structure IsRelativeOutgoingCompletion {η : Type*}
    (F : DirectedDiagram (d := d) h H ((ι ⊕ κ) ⊕ η)) : Prop where
  /-- The completion is an outgoing completion of the lifted quotient diagram and the ideal
  inputs. -/
  isOutgoingCompletion : IsOutgoingCompletion ((G.map sec hs).append W).wall F
  /-- Every added wall has a pure birth logarithm in the kernel of `π`. -/
  hasPureBirthLog : ∀ j, ∃ k, (F.wall (.inr j)).HasPureBirthLog {z | π z = 0} k

variable {π hπ sec hs G W}

/-- Lifting along a section and projecting recovers the quotient diagram. -/
theorem map_map_section (hsπ : ∀ x, π (sec x) = x) : (G.map sec hs).map π hπ = G := by
  have hid : π.compId sec = GradedLieHom.id ℳ := DFunLike.ext _ _ fun x => by simp [hsπ]
  simp [hid]

/-- Adjoining the ideal inputs to the lifted quotient diagram does not change its image under
`π`. -/
theorem map_append_map_equivalent (hsπ : ∀ x, π (sec x) = x)
    (hker : ∀ j, π.completedMap (W.wall j).label = 1) :
    (((G.map sec hs).append W).map π hπ).Equivalent G := by
  refine (equivalent_iff _ _).mpr fun k => ?_
  rw [map_append]
  simpa only [map_map_section hsπ] using
    ((G.map sec hs).map π hπ).append_levelEquivalent_left (W.map π hπ) (k := k)
      fun j => by simp [hker j]

section Existence

variable [Module.Free ℤ Γ]

/-- Every relative completion problem has a relative outgoing completion, whose image under `π`
is equivalent to the quotient diagram. -/
theorem exists_isRelativeOutgoingCompletion (hsπ : ∀ x, π (sec x) = x)
    (hGW : IsRelativeCompletionInput π G W) :
    ∃ (η : Type) (_ : Countable η) (F : DirectedDiagram (d := d) h H ((ι ⊕ κ) ⊕ η)),
      IsRelativeOutgoingCompletion π sec hs G W F ∧ (F.map π hπ).Equivalent G := by
  have hq := map_append_map_equivalent (hπ := hπ) (hs := hs) (G := G) hsπ
    hGW.completedMap_label_eq_one
  obtain ⟨η, hη, F, hF, hker, hFq⟩ := exists_relativeOutgoingCompletion sec hsπ hs
    (hq.symm.consistent hGW.consistent) (D := (G.map sec hs).append W) (hπ := hπ) (fun j => by
      rcases j with j | j
      · exact Or.inl ⟨(G.wall j).label, by simp⟩
      · simpa using Or.inr (hGW.exists_support_eq_hyperplane j))
  refine ⟨η, hη, F, ⟨hF, fun j => ?_⟩, hFq.trans hq⟩
  obtain ⟨n, hn, z, hz, hπz, hlabel, hactive⟩ := hker j
  exact ⟨(d.degree n).toNat, DirectedWall.hasPureBirthLog_def.mpr
    ⟨n, hn, Int.self_le_toNat _, z, hz, hπz, hlabel, fun l => by
      simpa only [mem_active] using hactive l⟩⟩

end Existence

/-- Two relative outgoing completions of equivalent quotient diagrams and equivalent ideal
inputs are equivalent. With `G = G'` and `W = W'` this is the uniqueness of the relative
outgoing completion. -/
theorem IsRelativeOutgoingCompletion.equivalent_of_equivalent {ι' κ' : Type z} {η η' : Type*}
    {G' : DirectedDiagram (d := d) h H' ι'} {W' : DirectedDiagram (d := d) h H κ'}
    {F : DirectedDiagram (d := d) h H ((ι ⊕ κ) ⊕ η)}
    {F' : DirectedDiagram (d := d) h H ((ι' ⊕ κ') ⊕ η')}
    (hF : IsRelativeOutgoingCompletion π sec hs G W F)
    (hF' : IsRelativeOutgoingCompletion π sec hs G' W' F')
    (hG : G.Equivalent G') (hW : W.Equivalent W') : F.Equivalent F' :=
  hF.isOutgoingCompletion.equivalent_of_initial_equivalent hF'.isOutgoingCompletion
    ((hG.map sec hs).append_congr hW)

/-- The finite-order form of `IsRelativeOutgoingCompletion.equivalent_of_equivalent`: relative
outgoing completions consistent at order `k` of order-`k` equivalent inputs agree at
order `k`. -/
theorem IsRelativeOutgoingCompletion.levelEquivalent_of_levelEquivalent
    {ι' κ' : Type z} {η η' : Type*}
    {G' : DirectedDiagram (d := d) h H' ι'} {W' : DirectedDiagram (d := d) h H κ'}
    {F : DirectedDiagram (d := d) h H ((ι ⊕ κ) ⊕ η)}
    {F' : DirectedDiagram (d := d) h H ((ι' ⊕ κ') ⊕ η')} {k : ℕ}
    (hF : IsRelativeOutgoingCompletion π sec hs G W F)
    (hF' : IsRelativeOutgoingCompletion π sec hs G' W' F')
    (hG : G.LevelEquivalent G' k) (hW : W.LevelEquivalent W' k) : F.LevelEquivalent F' k :=
  outgoingCompletion_levelEquivalent_of_initial_levelEquivalent
    ((hG.map sec hs).append_congr hW) hF.isOutgoingCompletion.wall_inl
    hF'.isOutgoingCompletion.wall_inl
    ((consistent_iff F).mp hF.isOutgoingCompletion.consistent k)
    ((consistent_iff F').mp hF'.isOutgoingCompletion.consistent k)
    (fun j _ => hF.isOutgoingCompletion.outgoing_inr j)
    (fun j _ => hF'.isOutgoingCompletion.outgoing_inr j)

section Class

variable [Module.Free ℤ Γ] (hπ hs) (hsπ : ∀ x, π (sec x) = x)

include hπ hs hsπ in
private theorem exists_relativeScat_class (hGW : IsRelativeCompletionInput π G W) :
    ∃ c : Class.{z} (d := d) (h := h) (H := H),
      ∃ (η : Type) (F : DirectedDiagram (d := d) h H ((ι ⊕ κ) ⊕ η)),
        IsRelativeOutgoingCompletion π sec hs G W F ∧ c = F.toClass := by
  obtain ⟨η, -, F, hF, -⟩ := exists_isRelativeOutgoingCompletion (hπ := hπ) hsπ hGW
  exact ⟨F.toClass, η, F, hF, rfl⟩

variable (π sec G W)

/-- The equivalence class of a relative outgoing completion of a relative completion problem. -/
def relativeScat (hGW : IsRelativeCompletionInput π G W) :
    Class.{z} (d := d) (h := h) (H := H) :=
  (exists_relativeScat_class hπ hs hsπ hGW).choose

variable {π sec G W}

/-- The relative scattering class has a representative that is a relative outgoing
completion. -/
theorem relativeScat_spec (hGW : IsRelativeCompletionInput π G W) :
    ∃ (η : Type) (F : DirectedDiagram (d := d) h H ((ι ⊕ κ) ⊕ η)),
      IsRelativeOutgoingCompletion π sec hs G W F ∧
        relativeScat π hπ sec hs G W hsπ hGW = F.toClass :=
  (exists_relativeScat_class hπ hs hsπ hGW).choose_spec

/-- Every relative outgoing completion represents the relative scattering class. -/
theorem relativeScat_eq_toClass (hGW : IsRelativeCompletionInput π G W) {η : Type z}
    {F : DirectedDiagram (d := d) h H ((ι ⊕ κ) ⊕ η)}
    (hF : IsRelativeOutgoingCompletion π sec hs G W F) :
    relativeScat π hπ sec hs G W hsπ hGW = F.toClass := by
  obtain ⟨η', F', hF', hc⟩ := relativeScat_spec hπ hs hsπ hGW
  exact hc.trans ((toClass_eq_iff F' F).mpr
    (hF'.equivalent_of_equivalent hF (Equivalent.refl G) (Equivalent.refl W)))

/-- The order-`k` relative scattering class depends only on the order-`k` classes of the
quotient diagram and of the ideal input. -/
theorem projection_relativeScat_eq_of_levelEquivalent {ι' κ' : Type z}
    {G' : DirectedDiagram (d := d) h H' ι'} {W' : DirectedDiagram (d := d) h H κ'}
    (hGW : IsRelativeCompletionInput π G W) (hGW' : IsRelativeCompletionInput π G' W')
    {k : ℕ} (hG : G.LevelEquivalent G' k) (hW : W.LevelEquivalent W' k) :
    (relativeScat π hπ sec hs G W hsπ hGW).projection k =
      (relativeScat π hπ sec hs G' W' hsπ hGW').projection k := by
  obtain ⟨η, F, hF, hc⟩ := relativeScat_spec hπ hs hsπ hGW
  obtain ⟨η', F', hF', hc'⟩ := relativeScat_spec hπ hs hsπ hGW'
  rw [hc, hc', Class.projection_toClass, Class.projection_toClass]
  exact (toLevelClass_eq_iff F F' k).mpr (hF.levelEquivalent_of_levelEquivalent hF' hG hW)

/-- Equivalent quotient diagrams and equivalent ideal inputs give the same relative scattering
class. -/
theorem relativeScat_eq_of_equivalent {ι' κ' : Type z}
    {G' : DirectedDiagram (d := d) h H' ι'} {W' : DirectedDiagram (d := d) h H κ'}
    (hGW : IsRelativeCompletionInput π G W) (hGW' : IsRelativeCompletionInput π G' W')
    (hG : G.Equivalent G') (hW : W.Equivalent W') :
    relativeScat π hπ sec hs G W hsπ hGW = relativeScat π hπ sec hs G' W' hsπ hGW' :=
  Class.ext fun k => projection_relativeScat_eq_of_levelEquivalent hπ hs hsπ hGW hGW'
    ((equivalent_iff _ _).mp hG k) ((equivalent_iff _ _).mp hW k)

end Class

section Map

variable {L₁ L₁' : Type w} [LieRing L₁] [LieAlgebra R L₁] [LieAlgebra ℚ L₁] [IsScalarTower ℚ R L₁]
  [LieRing L₁'] [LieAlgebra R L₁'] [LieAlgebra ℚ L₁'] [IsScalarTower ℚ R L₁']
  {ℒ₁ : Γ → Submodule R L₁} {ℳ₁ : Γ → Submodule R L₁'}
  [GradedLieAlgebra ℒ₁] [GradedLieAlgebra ℳ₁] [IsPositiveGrading d ℒ₁] [IsPositiveGrading d ℳ₁]
  {H₁ : DirectedWallSpaces ρ ℒ₁} {H₁' : DirectedWallSpaces ρ ℳ₁}
  {π₁ : GradedLieHom (PositiveDegreeMap.id d) ℒ₁ ℳ₁}
  {sec₁ : GradedLieHom (PositiveDegreeMap.id d) ℳ₁ ℒ₁}
  {hs₁ : ∀ n m, ∀ x ∈ H₁'.wall n m, sec₁ x ∈ H₁.wall n m}
  {f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℒ₁}
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H₁.wall n m)
  {g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℳ₁}
  (hg : ∀ n m, ∀ x ∈ H'.wall n m, g x ∈ H₁'.wall n m)

/-- A morphism of split extensions carries a relative completion problem to a relative
completion problem. -/
theorem IsRelativeCompletionInput.map (hGW : IsRelativeCompletionInput π G W)
    (hfπ : ∀ x, π₁ (f x) = g (π x)) :
    IsRelativeCompletionInput π₁ (G.map g hg) (W.map f hf) where
  consistent := hGW.consistent.map G g hg
  exists_support_eq_hyperplane j := by
    simpa only [map_wall, DirectedWall.map_support, DirectedWall.map_normal] using
      hGW.exists_support_eq_hyperplane j
  completedMap_label_eq_one j := by
    have hcomm : π₁.compId f = g.compId π := DFunLike.ext _ _ fun x => by simp [hfπ]
    have := DFunLike.congr_fun (congrArg GradedLieHom.completedMap hcomm) (W.wall j).label
    simp only [GradedLieHom.completedMap_compId, MonoidHom.comp_apply,
      hGW.completedMap_label_eq_one j, map_one] at this
    simpa only [map_wall, DirectedWall.map_label] using this

/-- Lifting along a section commutes with a morphism of split extensions. -/
theorem map_lift_append (hfsec : ∀ x, f (sec x) = sec₁ (g x)) :
    ((G.map sec hs).append W).map f hf = ((G.map g hg).map sec₁ hs₁).append (W.map f hf) := by
  have hcomm : f.compId sec = sec₁.compId g := DFunLike.ext _ _ fun x => by simp [hfsec]
  rw [map_append]
  congr 1
  apply DirectedDiagram.ext
  funext j
  have hlabel := DFunLike.congr_fun (congrArg GradedLieHom.completedMap hcomm) (G.wall j).label
  simp only [GradedLieHom.completedMap_compId, MonoidHom.comp_apply] at hlabel
  apply DirectedWall.ext <;> simp [hlabel]

variable [Module.Free ℤ Γ]

/-- The relative scattering class is natural in morphisms of split extensions that preserve
the wall spaces. -/
theorem map_relativeScat (hπ₁ : ∀ n m, ∀ x ∈ H₁.wall n m, π₁ x ∈ H₁'.wall n m)
    (hsπ : ∀ x, π (sec x) = x) (hsπ₁ : ∀ x, π₁ (sec₁ x) = x)
    (hfπ : ∀ x, π₁ (f x) = g (π x)) (hfsec : ∀ x, f (sec x) = sec₁ (g x))
    (hGW : IsRelativeCompletionInput π G W) :
    Class.map f hf (relativeScat π hπ sec hs G W hsπ hGW) =
      relativeScat π₁ hπ₁ sec₁ hs₁ (G.map g hg) (W.map f hf) hsπ₁ (hGW.map hf hg hfπ) := by
  obtain ⟨η, F, hF, hc⟩ := relativeScat_spec hπ hs hsπ hGW
  obtain ⟨η', F', hF', hc'⟩ := relativeScat_spec hπ₁ hs₁ hsπ₁ (hGW.map hf hg hfπ)
  rw [hc, hc', Class.map_toClass, toClass_eq_iff]
  have hwall : (fun j => (((G.map sec hs).append W).wall j).map f hf) =
      (((G.map g hg).map sec₁ hs₁).append (W.map f hf)).wall :=
    (funext (map_wall ((G.map sec hs).append W) f hf)).symm.trans
      (congrArg DirectedDiagram.wall (map_lift_append hf hg hfsec))
  have hF₀ := hF.isOutgoingCompletion.map f hf
  rw [hwall] at hF₀
  exact outgoingCompletion_unique hF₀ hF'.isOutgoingCompletion

end Map

end Mei.DirectedDiagram
