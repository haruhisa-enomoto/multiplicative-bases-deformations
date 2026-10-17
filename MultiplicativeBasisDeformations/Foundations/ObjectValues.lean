import MultiplicativeBasisDeformations.Foundations.ScalarAutomorphism
import MultiplicativeBasisDeformations.Foundations.DeckInstance
import MultiplicativeBasisDeformations.Foundations.MeshDegreeTwo
import MultiplicativeBasisDeformations.Foundations.CoverPotential
import MultiplicativeBasisDeformations.Foundations.SectionalPaths

/-!
# Lemma 4.13: weights on `L` are ratios of object values

`lem:scalar-object-values` (`scalar-normalization.tex`). For the deck
grading of a scalar mesh category with at most one arrow between two vertices,
a weight `d` on `L` gives the automorphism `Φ` of the cover
(`ScalarAutomorphism.lean`). "The endpoints of an arrow differ in height by one,
so the entire morphism space between them is spanned by the arrow. Thus
`Φ(a) = w(a) a` for some `w(a) ∈ k*`" (`wArr`). "Comparing coefficients gives
`w(σa) w(a) = ν_X`" (`mesh_compat`). "Assign `ν_X` to `t_X`. These weights
respect the triangles of `K̃`. Since this complex is simply connected,
multiplying along walks gives object values `ζ_X`" (`ζ`, `ζ_arrow`).
"Conjugation by these values fixes every arrow and hence every morphism, so `Φ`
multiplies each morphism `X̃ → Ỹ` by `ζ_Ỹ / ζ_X̃`" (`Φ_eq_ratio`), and on `L`
this gives `d(x, y) = ζ_y / ζ_x` (`weight_eq_ratio`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {v₀ : V}

/-! ### Sheets of walks from the basepoint -/

variable (Q v₀) in
/-- The lift of `X` in sheet `h`, as a walk class from the basepoint. -/
def liftW (h : Deck Q v₀) (X : V) : obC Q v₀ v₀ ⟶ obC Q v₀ X := h.unop ≫ coneC Q v₀ X

/-- The sheet of a walk class from the basepoint. -/
def sheet {X : V} (γ : obC Q v₀ v₀ ⟶ obC Q v₀ X) : Deck Q v₀ :=
  MulOpposite.op (γ ≫ Groupoid.inv (coneC Q v₀ X))

theorem sheet_liftW (h : Deck Q v₀) (X : V) : sheet (liftW Q v₀ h X) = h := by
  apply MulOpposite.unop_injective
  simp [sheet, liftW]

theorem liftW_arr (h : Deck Q v₀) {y x : V} (a : y ⟶ x) :
    liftW Q v₀ h y ≫ arrC Q v₀ a = liftW Q v₀ (h * (degW Q v₀).deg a.toPath) x := by
  simp only [liftW, degW_deg, MulOpposite.unop_mul, MulOpposite.unop_op, End.mul_def,
    pathC_toPath, Category.assoc, Groupoid.inv_comp, Category.comp_id]

theorem sheet_comp_arr {y x : V} (γ : obC Q v₀ v₀ ⟶ obC Q v₀ y) (a : y ⟶ x) :
    sheet (γ ≫ arrC Q v₀ a) = sheet γ * (degW Q v₀).deg a.toPath := by
  apply MulOpposite.unop_injective
  simp only [sheet, degW_deg, MulOpposite.unop_mul, MulOpposite.unop_op, End.mul_def,
    pathC_toPath, Category.assoc]
  rw [← Category.assoc (Groupoid.inv (coneC Q v₀ y)), Groupoid.inv_comp, Category.id_comp]

omit [Fintype V] [DecidableEq V] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] in
theorem path_length_one {y x : V} (p : Quiver.Path y x) (hp : p.length = 1) :
    ∃ b : y ⟶ x, p = b.toPath := by
  cases p with
  | nil => simp at hp
  | cons q b =>
      have hq : q.length = 0 := by simpa using hp
      obtain rfl := Quiver.Path.eq_of_length_zero q hq
      rw [Quiver.Path.eq_nil_of_length_zero q hq]
      exact ⟨b, rfl⟩

variable (Q c v₀) in
/-- The deck degree of an arrow. -/
abbrev dg {y x : V} (a : y ⟶ x) : Deck Q v₀ := (degW Q v₀).deg a.toPath

theorem arrowMor_ne_zero {y x : V} (a : y ⟶ x) : arrowMor c a ≠ 0 :=
  pathMor_ne_zero_of_isSectional c a.toPath (by
    unfold TranslationQuiver.IsSectional
    rw [Quiver.Path.arrowList_toPath]
    exact List.isChain_singleton _)

theorem arrow_mem (h : Deck Q v₀) {y x : V} (a : y ⟶ x) :
    arrowMor c a ∈ (deckGrading Q c v₀).part (h⁻¹ * (h * dg Q v₀ a)) y x := by
  rw [HomGrading.mem_part_iff, isHom_iff,
    show h⁻¹ * (h * dg Q v₀ a) = dg Q v₀ a from inv_mul_cancel_left h _]
  exact pathMor_mem_wPart a.toPath

/-- **Arrow lines**: the morphisms of the degree of an arrow are its multiples. -/
theorem part_arrow [hone : ∀ x y : V, Subsingleton (x ⟶ y)] {y x : V} (a : y ⟶ x)
    {g : obj c y ⟶ obj c x} (hg : g ∈ (deckGrading Q c v₀).part (dg Q v₀ a) y x) :
    ∃ t : k, g = t • arrowMor c a := by
  rw [HomGrading.mem_part_iff, isHom_iff] at hg
  have hsub : {f | ∃ p : Quiver.Path y x, (degW Q v₀).deg p = dg Q v₀ a ∧ pathMor c p = f} ⊆
      {arrowMor c a} := by
    rintro f ⟨p, hp, rfl⟩
    have hl := hgt_degW Q v₀ p
    rw [hp, hgt_degW Q v₀ a.toPath] at hl
    obtain ⟨b, rfl⟩ := path_length_one p (by simpa using hl.symm)
    rw [Subsingleton.elim b a]
    rfl
  have := Submodule.span_mono hsub (wPart_le_span Q c v₀ _ y x hg)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 this
  exact ⟨t, ht.symm⟩

/-! ### The automorphism `Φ` on arrows and meshes -/

variable [IsAlgClosed k] [Infinite k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  {d : D.PV × Deck Q v₀ → D.PV × Deck Q v₀ → k}
  (hd : Thin.IsWeight (O := CovObj (grading0 D (deckGrading Q c v₀))) Set.univ d)

include hd hF in
/-- **`Φ(a) = w(a) a`**: the scalar of `Φ` on the lift of an arrow in sheet `h`. -/
def wArr (h : Deck Q v₀) {y x : V} (a : y ⟶ x) : k :=
  Classical.choose (part_arrow (c := c) a (by
    have := Φ_mem hd (deckHeight Q c v₀) hF (X := (y, h)) (Y := (x, h * dg Q v₀ a)) _
      (arrow_mem h a)
    rwa [show h⁻¹ * (h * dg Q v₀ a) = dg Q v₀ a from inv_mul_cancel_left h _] at this))

theorem wArr_spec (h : Deck Q v₀) {y x : V} (a : y ⟶ x) :
    Φ hd (deckHeight Q c v₀) hF (X := (y, h)) (Y := (x, h * dg Q v₀ a)) (arrowMor c a)
      (arrow_mem h a) = wArr hF hd h a • arrowMor c a :=
  Classical.choose_spec (part_arrow (c := c) a (by
    have := Φ_mem hd (deckHeight Q c v₀) hF (X := (y, h)) (Y := (x, h * dg Q v₀ a)) _
      (arrow_mem h a)
    rwa [show h⁻¹ * (h * dg Q v₀ a) = dg Q v₀ a from inv_mul_cancel_left h _] at this))

theorem wArr_ne (h : Deck Q v₀) {y x : V} (a : y ⟶ x) : wArr hF hd h a ≠ 0 := by
  intro h0
  apply arrowMor_ne_zero (c := c) a
  apply eq_zero_of_Φ hd (deckHeight Q c v₀) hF (X := (y, h)) (Y := (x, h * dg Q v₀ a)) _
    (arrow_mem h a)
  rw [wArr_spec, h0, zero_smul]

theorem Φ_cast {X : V × Deck Q v₀} {y : V} {g g' : Deck Q v₀} (hg : g = g')
    {f f' : obj c X.1 ⟶ obj c y} (hf : f = f')
    (h1 : f ∈ (deckGrading Q c v₀).part (X.2⁻¹ * g) X.1 y)
    (h2 : f' ∈ (deckGrading Q c v₀).part (X.2⁻¹ * g') X.1 y) :
    Φ hd (deckHeight Q c v₀) hF (Y := (y, g)) f h1 =
      Φ hd (deckHeight Q c v₀) hF (Y := (y, g')) f' h2 := by
  subst hg hf; rfl

theorem Φ_zero {X Y : V × Deck Q v₀} (h0 : (0 : obj c X.1 ⟶ obj c Y.1) ∈
    (deckGrading Q c v₀).part (X.2⁻¹ * Y.2) X.1 Y.1) :
    Φ hd (deckHeight Q c v₀) hF (0 : obj c X.1 ⟶ obj c Y.1) h0 = 0 := by
  have h1 := Φ_smul hd (deckHeight Q c v₀) hF 0 (0 : obj c X.1 ⟶ obj c Y.1) h0
  calc Φ hd (deckHeight Q c v₀) hF (0 : obj c X.1 ⟶ obj c Y.1) h0 =
        Φ hd (deckHeight Q c v₀) hF ((0 : k) • (0 : obj c X.1 ⟶ obj c Y.1))
          (Submodule.smul_mem _ 0 h0) := Φ_cast hF hd rfl (zero_smul k _).symm _ _
    _ = 0 := by rw [h1, zero_smul]

theorem Φ_sum {X Y : V × Deck Q v₀} {ι : Type} (s : Finset ι)
    (f : ι → (obj c X.1 ⟶ obj c Y.1))
    (hf : ∀ i, f i ∈ (deckGrading Q c v₀).part (X.2⁻¹ * Y.2) X.1 Y.1) :
    Φ hd (deckHeight Q c v₀) hF (∑ i ∈ s, f i) (Submodule.sum_mem _ fun i _ ↦ hf i) =
      ∑ i ∈ s, Φ hd (deckHeight Q c v₀) hF (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Φ_zero hF hd _
  | insert i s hi ih =>
      calc Φ hd (deckHeight Q c v₀) hF (∑ j ∈ insert i s, f j) _ =
            Φ hd (deckHeight Q c v₀) hF (f i + ∑ j ∈ s, f j)
              (add_mem (hf i) (Submodule.sum_mem _ fun j _ ↦ hf j)) :=
            Φ_cast hF hd rfl (Finset.sum_insert hi) _ _
        _ = _ := by
            rw [Φ_add hd (deckHeight Q c v₀) hF (f i) _ (hf i)
              (Submodule.sum_mem _ fun j _ ↦ hf j), ih, Finset.sum_insert hi]

/-- The deck degree of the translation edge `t_x`. -/
def tdeg (x : Q.nonprojective) : Deck Q v₀ :=
  MulOpposite.op (coneC Q v₀ (Q.tau x).1 ≫ tC Q v₀ x ≫ Groupoid.inv (coneC Q v₀ x.1))

omit [Fintype V] [DecidableEq V] in
theorem dg_mesh (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) :
    dg Q v₀ (Q.mate x a.1 a.2) * dg Q v₀ a.2 = tdeg x := by
  refine ((degW Q v₀).deg_comp _ _).symm.trans ?_
  rw [degW_deg, pathC_comp, pathC_toPath, pathC_toPath, tri_rel Q v₀ x a]
  rfl

/-- **Compatibility at a mesh**: `w(σa) w(a) = ν_X` for every mate pair. -/
theorem mesh_compat (x : Q.nonprojective) (h : Deck Q v₀) :
    ∃ ν : k, ∀ a : Σ y : V, y ⟶ x.1,
      wArr hF hd h (Q.mate x a.1 a.2) * wArr hF hd (h * dg Q v₀ (Q.mate x a.1 a.2)) a.2 = ν := by
  set H := deckHeight Q c v₀
  have e : ∀ a : Σ y : V, y ⟶ x.1,
      h * dg Q v₀ (Q.mate x a.1 a.2) * dg Q v₀ a.2 = h * tdeg x :=
    fun a ↦ (mul_assoc _ _ _).trans (congrArg (h * ·) (dg_mesh x a))
  have mem2 : ∀ a : Σ y : V, y ⟶ x.1, arrowMor c a.2 ∈ (deckGrading Q c v₀).part
      ((h * dg Q v₀ (Q.mate x a.1 a.2))⁻¹ * (h * tdeg x)) a.1 x.1 := fun a ↦ by
    have := arrow_mem (c := c) (h * dg Q v₀ (Q.mate x a.1 a.2)) a.2
    rwa [e a] at this
  have mem : ∀ a : Σ y : V, y ⟶ x.1, arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2 ∈
      (deckGrading Q c v₀).part (h⁻¹ * (h * tdeg x)) (Q.tau x).1 x.1 :=
    fun a ↦ comp_mem (arrow_mem h _) (mem2 a)
  set ww : (Σ y : V, y ⟶ x.1) → k := fun a ↦
    wArr hF hd h (Q.mate x a.1 a.2) * wArr hF hd (h * dg Q v₀ (Q.mate x a.1 a.2)) a.2
  have hΦa : ∀ a : Σ y : V, y ⟶ x.1,
      Φ hd H hF (X := ((Q.tau x).1, h)) (Y := (x.1, h * tdeg x)) _ (mem a) =
        ww a • (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) := by
    intro a
    rw [Φ_comp hd H hF (X := ((Q.tau x).1, h)) (Y := (a.1, h * dg Q v₀ (Q.mate x a.1 a.2)))
      (Z := (x.1, h * tdeg x)) _ (arrow_mem h _) _ (mem2 a), wArr_spec,
      Φ_cast hF hd (X := (a.1, h * dg Q v₀ (Q.mate x a.1 a.2))) (y := x.1) (e a).symm rfl
        (mem2 a) (arrow_mem _ a.2), wArr_spec,
      Linear.smul_comp, Linear.comp_smul, smul_smul]
  have hzero : ∑ a : (Σ y : V, y ⟶ x.1), (((c x a.1 a.2 : kˣ) : k) * ww a) •
      (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) = 0 := by
    have hsm : ∀ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
        (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) ∈
        (deckGrading Q c v₀).part (h⁻¹ * (h * tdeg x)) (Q.tau x).1 x.1 :=
      fun a ↦ Submodule.smul_mem _ _ (mem a)
    have h1 := Φ_sum hF hd (X := ((Q.tau x).1, h)) (Y := (x.1, h * tdeg x)) Finset.univ _ hsm
    have h2 : Φ hd H hF (X := ((Q.tau x).1, h)) (Y := (x.1, h * tdeg x))
        (∑ a : (Σ y : V, y ⟶ x.1), ((c x a.1 a.2 : kˣ) : k) •
          (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2))
        (Submodule.sum_mem _ fun a _ ↦ hsm a) = 0 :=
      (Φ_cast hF hd (X := ((Q.tau x).1, h)) (y := x.1) rfl (mesh_sum_zero c x) _
        (Submodule.zero_mem _)).trans (Φ_zero hF hd (X := ((Q.tau x).1, h)) (Y := (x.1, h * tdeg x)) _)
    rw [h2] at h1
    refine Eq.trans ?_ h1.symm
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Φ_smul hd H hF (X := ((Q.tau x).1, h)) (Y := (x.1, h * tdeg x)) _ _ (mem a), hΦa,
      smul_smul]
  obtain ⟨ν, hν⟩ := mesh_coeffs c x _ hzero
  refine ⟨ν, fun a ↦ ?_⟩
  have := hν a
  rw [mul_comm ν] at this
  exact mul_left_cancel₀ (Units.ne_zero _) this

/-! ### Object values by simple connectivity -/

open scoped Classical in
include hF hd in
/-- The value `ν_X` assigned to the translation edge `t_X` in a sheet. -/
def νv (h : Deck Q v₀) (x : Q.nonprojective) : k :=
  if hm : Nonempty (Σ y : V, y ⟶ x.1) then
    wArr hF hd h (Q.mate x hm.some.1 hm.some.2) *
      wArr hF hd (h * dg Q v₀ (Q.mate x hm.some.1 hm.some.2)) hm.some.2
  else 1

theorem νv_eq (h : Deck Q v₀) (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) :
    wArr hF hd h (Q.mate x a.1 a.2) * wArr hF hd (h * dg Q v₀ (Q.mate x a.1 a.2)) a.2 =
      νv hF hd h x := by
  obtain ⟨ν, hν⟩ := mesh_compat hF hd x h
  rw [νv, dif_pos ⟨a⟩, hν, hν]

theorem νv_ne (h : Deck Q v₀) (x : Q.nonprojective) : νv hF hd h x ≠ 0 := by
  rw [νv]
  split_ifs
  · exact mul_ne_zero (wArr_ne hF hd _ _) (wArr_ne hF hd _ _)
  · exact one_ne_zero

include hF hd in
/-- **The weights on the edges of the lifted complex**: `w(a)` on arrows, `ν_X`
on translation edges, one on cone edges. -/
def Wt : ∀ e : Ed Q ⊕ V, (obC Q v₀ v₀ ⟶ obC Q v₀ (srcC Q v₀ e)) → kˣ
  | Sum.inl (Sum.inl ⟨_, _, a⟩), γ => Units.mk0 (wArr hF hd (sheet γ) a) (wArr_ne hF hd _ _)
  | Sum.inl (Sum.inr x), γ => Units.mk0 (νv hF hd (sheet γ) x) (νv_ne hF hd _ _)
  | Sum.inr _, _ => 1

/-- **The weights respect the triangles.** -/
theorem Wt_tri (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1)
    (γ : obC Q v₀ v₀ ⟶ obC Q v₀ (Q.tau x).1) :
    Wt hF hd (Sum.inl (Sum.inl ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩)) γ *
      Wt hF hd (Sum.inl (Sum.inl ⟨a.1, x.1, a.2⟩)) (γ ≫ arrC Q v₀ (Q.mate x a.1 a.2)) =
    Wt hF hd (Sum.inl (Sum.inr x)) γ := by
  apply Units.ext
  change wArr hF hd (sheet γ) (Q.mate x a.1 a.2) *
    wArr hF hd (sheet (γ ≫ arrC Q v₀ (Q.mate x a.1 a.2))) a.2 = νv hF hd (sheet γ) x
  rw [sheet_comp_arr, νv_eq]

include hF hd in
/-- **The object values** `ζ` on the lifted vertices. -/
def ζ (X : V × Deck Q v₀) : kˣ := potW (Wt hF hd) (Wt_tri hF hd) (liftW Q v₀ X.2 X.1)

/-- `w(a) = ζ_{target(a)} / ζ_{source(a)}`. -/
theorem ζ_arrow (h : Deck Q v₀) {y x : V} (a : y ⟶ x) :
    (ζ hF hd (x, h * dg Q v₀ a) : k) = ζ hF hd (y, h) * wArr hF hd h a := by
  have := potW_comp (Wt hF hd) (Wt_tri hF hd) (Sum.inl (Sum.inl ⟨y, x, a⟩)) (liftW Q v₀ h y)
  change potW (Wt hF hd) (Wt_tri hF hd) (liftW Q v₀ h y ≫ arrC Q v₀ a) = _ at this
  rw [liftW_arr] at this
  unfold ζ
  rw [this]
  change ((potW (Wt hF hd) (Wt_tri hF hd) (liftW Q v₀ h y) : kˣ) : k) *
    wArr hF hd (sheet (liftW Q v₀ h y)) a = _
  rw [sheet_liftW]

/-! ### Conjugation by the object values -/

theorem pathMor_mem (X : V × Deck Q v₀) {y : V} (p : Quiver.Path X.1 y) :
    pathMor c p ∈ (deckGrading Q c v₀).part (X.2⁻¹ * (X.2 * (degW Q v₀).deg p)) X.1 y := by
  rw [HomGrading.mem_part_iff, isHom_iff,
    show X.2⁻¹ * (X.2 * (degW Q v₀).deg p) = (degW Q v₀).deg p from
      inv_mul_cancel_left X.2 ((degW Q v₀).deg p)]
  exact pathMor_mem_wPart p

/-- **`Φ` on paths**: the lift of a path is multiplied by `ζ_Ỹ / ζ_X̃`. -/
theorem Φ_path (X : V × Deck Q v₀) {y : V} (p : Quiver.Path X.1 y) :
    Φ hd (deckHeight Q c v₀) hF (X := X) (Y := (y, X.2 * (degW Q v₀).deg p)) (pathMor c p)
      (pathMor_mem X p) =
    ((ζ hF hd (y, X.2 * (degW Q v₀).deg p) : k) / ζ hF hd X) • pathMor c p := by
  induction p with
  | nil =>
      have hg1 : X.2 * (degW Q v₀).deg (Quiver.Path.nil : Quiver.Path X.1 X.1) = X.2 :=
        (congrArg (X.2 * ·) ((degW Q v₀).deg_nil X.1)).trans (mul_one _)
      have hid : 𝟙 (obj c X.1) ∈ (deckGrading Q c v₀).part (X.2⁻¹ * X.2) X.1 X.1 := by
        rw [HomGrading.mem_part_iff, show X.2⁻¹ * X.2 = 1 from inv_mul_cancel X.2]
        exact HomGrading.isHom_id _ _
      rw [Φ_cast hF hd (X := X) (y := X.1) hg1 (pathMor_nil Q c X.1) _ hid]
      have h1 := Φ_id hd (deckHeight Q c v₀) hF (X := X) hid
      refine h1.trans ?_
      have hζ : ζ hF hd (X.1, X.2 * (degW Q v₀).deg (Quiver.Path.nil : Quiver.Path X.1 X.1)) =
          ζ hF hd X := congrArg (ζ hF hd) (Prod.ext rfl hg1)
      rw [hζ, div_self (Units.ne_zero _), one_smul, pathMor_nil]
  | cons p' a ih =>
      rename_i z y
      set Z : V × Deck Q v₀ := (z, X.2 * (degW Q v₀).deg p')
      have hdeg : X.2 * (degW Q v₀).deg (p'.cons a) = Z.2 * dg Q v₀ a :=
        (congrArg (X.2 * ·) ((degW Q v₀).deg_comp p' a.toPath)).trans (mul_assoc _ _ _).symm
      have hcons : pathMor c (p'.cons a) = pathMor c p' ≫ arrowMor c a := pathMor_cons c p' a
      rw [Φ_cast hF hd (X := X) (y := y) hdeg hcons _ (comp_mem (pathMor_mem X p') (arrow_mem Z.2 a)),
        Φ_comp hd (deckHeight Q c v₀) hF (X := X) (Y := Z) (Z := (y, Z.2 * dg Q v₀ a)) _
          (pathMor_mem X p') _ (arrow_mem Z.2 a), ih, wArr_spec, Linear.smul_comp, Linear.comp_smul,
        smul_smul, hcons]
      congr 1
      have hζ : ζ hF hd (y, X.2 * (degW Q v₀).deg (p'.cons a)) = ζ hF hd (y, Z.2 * dg Q v₀ a) :=
        congrArg (ζ hF hd) (Prod.ext rfl hdeg)
      rw [hζ, ζ_arrow hF hd Z.2 a]
      field_simp
      rfl

/-- **Conjugation**: `Φ` multiplies each morphism `X̃ → Ỹ` by `ζ_Ỹ / ζ_X̃`. -/
theorem Φ_eq_ratio (X Y : V × Deck Q v₀) (f : obj c X.1 ⟶ obj c Y.1)
    (hf : f ∈ (deckGrading Q c v₀).part (X.2⁻¹ * Y.2) X.1 Y.1) :
    Φ hd (deckHeight Q c v₀) hF f hf = ((ζ hF hd Y : k) / ζ hF hd X) • f := by
  have hspan := wPart_le_span Q c v₀ _ _ _
    ((isHom_iff Q c v₀).1 ((HomGrading.mem_part_iff _).1 hf))
  have hle : Submodule.span k {f | ∃ p : Quiver.Path X.1 Y.1,
      (degW Q v₀).deg p = X.2⁻¹ * Y.2 ∧ pathMor c p = f} ≤
      (deckGrading Q c v₀).part (X.2⁻¹ * Y.2) X.1 Y.1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, HomGrading.mem_part_iff, isHom_iff Q c v₀, ← hp]
    exact pathMor_mem_wPart p
  revert hf
  refine Submodule.span_induction (p := fun f _ ↦ ∀ hf, Φ hd (deckHeight Q c v₀) hF f hf =
    ((ζ hF hd Y : k) / ζ hF hd X) • f) ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨p, hp, rfl⟩ hf
    have hY : X.2 * (degW Q v₀).deg p = Y.2 := by
      rw [hp]; exact mul_inv_cancel_left X.2 Y.2
    have h1 := Φ_path hF hd X p
    rw [Φ_cast hF hd (X := X) (y := Y.1) hY rfl (pathMor_mem X p) hf] at h1
    have hζ : ζ hF hd (Y.1, X.2 * (degW Q v₀).deg p) = ζ hF hd Y :=
      congrArg (ζ hF hd) (Prod.ext rfl hY)
    rw [hζ] at h1
    exact h1
  · intro hf
    rw [Φ_zero hF hd hf, smul_zero]
  · intro f g hfs hgs ihf ihg hfg
    rw [Φ_add hd (deckHeight Q c v₀) hF f g (hle hfs) (hle hgs), ihf (hle hfs), ihg (hle hgs),
      smul_add]
  · intro t f hfs ih hf
    rw [Φ_smul hd (deckHeight Q c v₀) hF t f (hle hfs), ih (hle hfs), smul_comm]

include hF hd in
/-- **Lemma 4.13**: every multiplicative scalar weight on `L` is a ratio of
object values, `d(x, y) = ζ_y / ζ_x` on every nonzero morphism line. -/
theorem weight_eq_ratio : ∃ ζ' : D.PV × Deck Q v₀ → k, (∀ z, ζ' z ≠ 0) ∧
    ∀ (z₁ z₂ : D.PV × Deck Q v₀) (f : obj c z₁.1.1 ⟶ obj c z₂.1.1),
      f ∈ (deckGrading Q c v₀).part (z₁.2⁻¹ * z₂.2) z₁.1.1 z₂.1.1 → f ≠ 0 →
        d z₁ z₂ = ζ' z₂ / ζ' z₁ := by
  refine ⟨fun z ↦ (ζ hF hd (z.1.1, z.2) : k), fun z ↦ Units.ne_zero _, fun z₁ z₂ f hf hf0 ↦ ?_⟩
  have h1 := Φ_proj hd (deckHeight Q c v₀) hF z₁ z₂ f hf
  have h2 := Φ_eq_ratio hF hd (z₁.1.1, z₁.2) (z₂.1.1, z₂.2) f hf
  rw [h1] at h2
  exact smul_left_injective k hf0 h2

end MeshWalk

end MultiplicativeBasisDeformations
