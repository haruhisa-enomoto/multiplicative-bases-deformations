import MultiplicativeBasisDeformations.Foundations.RightModules
import MBDVendor.Magnitude.Algebra.RightModuleIntrinsicArrowMultiplicity
import MBDVendor.Magnitude.CategoryTheory.AlmostSplitSummandIrreducible

/-!
# Bridge to the vendored Auslander--Reiten theory

The vendored library `MBDVendor` (general Auslander--Reiten theory, copied
from the magnitude-conjecture formalization) works with finitely generated right
modules `FGModuleCat Aᵐᵒᵖ` and with the radical of that whole category. This
file connects it with the manuscript-literal objects of
`Foundations/RightModules.lean`:

* an `IndSkeleton` is a vendored `FiniteIndecomposableSkeleton`;
* `ind(mod A)` embeds fully faithfully into `mod A = FGModuleCat Aᵐᵒᵖ`;
* the radical morphisms of `ind(mod A)` are the vendored radical morphisms;
* `J²(X, Y)`, defined through indecomposable intermediate objects, is the
  vendored radical square, defined through arbitrary finitely generated
  intermediate modules;
* hence `Irr(X, Y)` is linearly isomorphic to the vendored irreducible space.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- `mod A`: finitely generated right `A`-modules. -/
abbrev ModCat (A : Type u) [Ring A] := FGModuleCat.{u} Aᵐᵒᵖ

/-- A composite through an object with a finite biproduct decomposition is the
sum of the composites through the summands. -/
theorem comp_eq_sum_biproduct {C : Type*} [Category C] [Preadditive C]
    {ι : Type} [Fintype ι] {F : ι → C} [HasBiproduct F] {X M Y : C}
    (e : M ≅ ⨁ F) (a : X ⟶ M) (b : M ⟶ Y) :
    a ≫ b = ∑ i, (a ≫ e.hom ≫ biproduct.π F i) ≫ (biproduct.ι F i ≫ e.inv ≫ b) := by
  calc a ≫ b = a ≫ e.hom ≫ 𝟙 (⨁ F) ≫ e.inv ≫ b := by simp
    _ = a ≫ e.hom ≫ (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ e.inv ≫ b := by
        simp only [biproduct.total]
    _ = _ := by
        simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]

namespace IndSkeleton

variable (S : IndSkeleton k A)

/-- An indecomposable skeleton, as a skeleton of the vendored library. -/
abbrev toVendor : MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton k A where
  n := S.n
  obj := S.obj
  obj_finite i := (S.isFiniteIndecomposable i).1
  obj_indecomposable i := (S.isFiniteIndecomposable i).2
  eq_of_iso h := S.pairwise _ _ h
  complete M hM := S.complete M hM

@[simp] theorem toVendor_n : S.toVendor.n = S.n := rfl

@[simp] theorem toVendor_obj (i : Fin S.n) : S.toVendor.obj i = S.obj i := rfl

/-- The object of `mod A` labelled by an index. -/
abbrev fg (x : Fin S.n) : ModCat A := S.toVendor.fgObj x

/-- The full embedding `ind(mod A) → mod A`. -/
def toFG : S.Ind ⥤ ModCat A where
  obj x := S.fg x
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

instance : S.toFG.Full where
  map_surjective f := ⟨InducedCategory.homMk f.hom, rfl⟩

instance : S.toFG.Faithful where
  map_injective {X Y} f g h := by
    ext1
    exact congrArg (fun q : S.fg X ⟶ S.fg Y ↦ q.hom) h

instance : S.toFG.Additive where
  map_add := rfl

instance : S.toFG.Linear k where
  map_smul _ _ := rfl

/-- `ind(mod A) → mod A` on Hom spaces, as a `k`-linear equivalence. -/
def homEquivFG (X Y : S.Ind) : (X ⟶ Y) ≃ₗ[k] (S.toFG.obj X ⟶ S.toFG.obj Y) :=
  { S.toFG.mapLinearMap k with
    invFun := S.toFG.preimage
    left_inv := fun f ↦ S.toFG.preimage_map f
    right_inv := fun g ↦ S.toFG.map_preimage g }

@[simp] theorem homEquivFG_apply {X Y : S.Ind} (f : X ⟶ Y) :
    S.homEquivFG X Y f = S.toFG.map f := rfl

open MBDVendor.QSE.CategoricalRadical in
/-- A morphism of `ind(mod A)` is radical exactly when its image in `mod A` is
a radical morphism in the sense of the vendored library. -/
theorem isRadical_iff {X Y : S.Ind} (f : X ⟶ Y) :
    S.IsRadical f ↔ IsRadicalMorphism (S.toFG.map f) := by
  constructor
  · intro hf g
    obtain ⟨g', rfl⟩ := S.toFG.map_surjective g
    have := hf g'
    have h : S.toFG.map (𝟙 X - f ≫ g') = 𝟙 _ - S.toFG.map f ≫ S.toFG.map g' := by
      simp [Functor.map_sub]
    rw [← h]
    infer_instance
  · intro hf g
    have h : S.toFG.map (𝟙 X - f ≫ g) = 𝟙 _ - S.toFG.map f ≫ S.toFG.map g := by
      simp [Functor.map_sub]
    have : IsIso (S.toFG.map (𝟙 X - f ≫ g)) := by rw [h]; exact hf _
    exact isIso_of_fully_faithful S.toFG _

open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal in
/-- `J(X, Y)` consists exactly of the radical morphisms. -/
theorem mem_radPow_one_iff {X Y : S.Ind} (f : X ⟶ Y) :
    f ∈ S.radPow 1 X Y ↔ S.IsRadical f := by
  constructor
  · intro hf
    rw [isRadical_iff]
    change f ∈ Submodule.span k _ at hf
    induction hf using Submodule.span_induction with
    | mem h hh =>
        obtain ⟨Z, f₁, g, hf₁, -, rfl⟩ := hh
        rw [Functor.map_comp]
        exact isRadicalMorphism_postcomp _ ((S.isRadical_iff f₁).1 hf₁)
    | zero =>
        rw [Functor.map_zero]
        exact isRadicalMorphism_zero
    | add a b _ _ ha hb => simpa using isRadicalMorphism_add ha hb
    | smul c a _ ha =>
        have h : S.toFG.map (c • a) = (c • 𝟙 _) ≫ S.toFG.map a := by
          simp [Functor.map_smul]
        rw [h]
        exact isRadicalMorphism_precomp _ ha
  · intro hf
    apply Submodule.subset_span
    exact ⟨Y, f, 𝟙 Y, hf, Submodule.mem_top, by simp⟩

/-- The radical square of the vendored library: the additive subgroup
generated by composites of two radical morphisms through arbitrary objects of
`mod A`. -/
abbrev vendorRadicalSquare (X Y : S.Ind) :=
  (MBDVendor.QSE.CategoricalRadical.homIdeal ⋆ᵢ
      MBDVendor.QSE.CategoricalRadical.homIdeal :
    MBDVendor.QSE.CategoricalIdeal.HomIdeal (ModCat A)).hom (S.toFG.obj X) (S.toFG.obj Y)

/-- Mapping back and forth along the embedding into `mod A`. -/
theorem map_homEquivFG_symm {X Y : S.Ind} (g : S.toFG.obj X ⟶ S.toFG.obj Y) :
    S.toFG.map ((S.homEquivFG X Y).symm g) = g :=
  (S.homEquivFG X Y).apply_symm_apply g

section Noetherian

variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal in
/-- `J²(X, Y)`, defined through indecomposable intermediate objects, is the
vendored radical square, defined through arbitrary finitely generated
intermediate modules. -/
theorem mem_radPow_two_iff {X Y : S.Ind} (f : X ⟶ Y) :
    f ∈ S.radPow 2 X Y ↔ S.toFG.map f ∈ S.vendorRadicalSquare X Y := by
  constructor
  · intro hf
    change f ∈ Submodule.span k _ at hf
    induction hf using Submodule.span_induction with
    | mem h hh =>
        obtain ⟨Z, f₁, g, hf₁, hg, rfl⟩ := hh
        rw [Functor.map_comp]
        exact HomIdeal.comp_mem_mul ((S.isRadical_iff f₁).1 hf₁)
          ((S.isRadical_iff g).1 ((S.mem_radPow_one_iff g).1 hg))
    | zero => rw [Functor.map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [Functor.map_add]; exact add_mem ha hb
    | smul c a _ ha =>
        have h : S.toFG.map (c • a) = (c • 𝟙 _) ≫ S.toFG.map a := by
          simp [Functor.map_smul]
        rw [h]
        exact (homIdeal ⋆ᵢ homIdeal).precomp _ ha
  · intro hf
    suffices H : ∀ h ∈ S.vendorRadicalSquare X Y,
        (S.homEquivFG X Y).symm h ∈ S.radPow 2 X Y by
      have h := H _ hf
      rwa [← homEquivFG_apply, LinearEquiv.symm_apply_apply] at h
    intro h hh
    induction hh using AddSubgroup.closure_induction with
    | mem h hh =>
        obtain ⟨M, a, b, ha, hb, rfl⟩ := hh
        obtain ⟨n, label, ⟨e⟩⟩ := S.toVendor.fgObj_decomposition (k := k) M
        rw [comp_eq_sum_biproduct e a b, map_sum]
        refine Submodule.sum_mem _ fun i _ ↦ ?_
        let a' : X ⟶ S.ind (label i) :=
          (S.homEquivFG X (S.ind (label i))).symm
            (a ≫ e.hom ≫ biproduct.π (fun j ↦ S.toVendor.fgObj (label j)) i)
        let b' : S.ind (label i) ⟶ Y :=
          (S.homEquivFG (S.ind (label i)) Y).symm
            (biproduct.ι (fun j ↦ S.toVendor.fgObj (label j)) i ≫ e.inv ≫ b)
        have ha' : S.toFG.map a' =
            a ≫ e.hom ≫ biproduct.π (fun j ↦ S.toVendor.fgObj (label j)) i :=
          S.map_homEquivFG_symm _
        have hb' : S.toFG.map b' =
            biproduct.ι (fun j ↦ S.toVendor.fgObj (label j)) i ≫ e.inv ≫ b :=
          S.map_homEquivFG_symm _
        have hterm : (a ≫ e.hom ≫ biproduct.π (fun j ↦ S.toVendor.fgObj (label j)) i) ≫
            (biproduct.ι (fun j ↦ S.toVendor.fgObj (label j)) i ≫ e.inv ≫ b) =
              S.homEquivFG X Y (a' ≫ b') := by
          rw [homEquivFG_apply, Functor.map_comp, ha', hb']
          rfl
        rw [hterm, LinearEquiv.symm_apply_apply]
        apply Submodule.subset_span
        refine ⟨S.ind (label i), a', b', ?_, ?_, rfl⟩
        · rw [isRadical_iff, ha']
          exact isRadicalMorphism_postcomp _ ha
        · rw [mem_radPow_one_iff, isRadical_iff, hb']
          exact isRadicalMorphism_precomp _ (isRadicalMorphism_precomp e.inv hb)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha

/-- The vendored intrinsic irreducible space `rad(X, Y) / rad²(X, Y)` of
`mod A`, at two labelled indecomposables. -/
abbrev vendorIrr (X Y : S.Ind) :=
  MBDVendor.Magnitude.CategoricalIrreducible.Space k (S.toFG.obj X) (S.toFG.obj Y)

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
open MBDVendor.Magnitude in
theorem radPow_one_map_eq (X Y : S.Ind) :
    (S.radPow 1 X Y).map (S.homEquivFG X Y).toLinearMap =
      CategoricalIrreducible.radical k (S.toFG.obj X) (S.toFG.obj Y) := by
  ext g
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    change S.toFG.map f ∈ MBDVendor.QSE.CategoricalRadical.homIdeal.hom _ _
    rw [MBDVendor.QSE.CategoricalRadical.mem_homIdeal_iff, ← isRadical_iff]
    exact (S.mem_radPow_one_iff f).1 hf
  · intro hg
    refine ⟨(S.homEquivFG X Y).symm g, ?_, (S.homEquivFG X Y).apply_symm_apply g⟩
    rw [mem_radPow_one_iff, isRadical_iff, map_homEquivFG_symm]
    exact (MBDVendor.QSE.CategoricalRadical.mem_homIdeal_iff g).1 hg

/-- `J(X, Y)` and the vendored radical, as linearly equivalent spaces. -/
def radPowOneEquiv (X Y : S.Ind) :
    S.radPow 1 X Y ≃ₗ[k]
      MBDVendor.Magnitude.CategoricalIrreducible.radical k (S.toFG.obj X) (S.toFG.obj Y) :=
  ((S.homEquivFG X Y).submoduleMap (S.radPow 1 X Y)).trans
    (LinearEquiv.ofEq _ _ (S.radPow_one_map_eq X Y))

/-- `Irr(X, Y)` is linearly isomorphic to the vendored irreducible space. -/
def irrEquivVendor (X Y : S.Ind) : S.Irr X Y ≃ₗ[k] S.vendorIrr X Y :=
  Submodule.Quotient.equiv _ _ (S.radPowOneEquiv X Y) (by
    ext g
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨f, hf, rfl⟩
      change S.toFG.map f.1 ∈ S.vendorRadicalSquare X Y
      exact (S.mem_radPow_two_iff f.1).1 hf
    · intro hg
      refine ⟨(S.radPowOneEquiv X Y).symm g, ?_, (S.radPowOneEquiv X Y).apply_symm_apply g⟩
      change ((S.radPowOneEquiv X Y).symm g).1 ∈ S.radPow 2 X Y
      rw [mem_radPow_two_iff]
      have : S.toFG.map ((S.radPowOneEquiv X Y).symm g).1 = g.1 :=
        congrArg Subtype.val ((S.radPowOneEquiv X Y).apply_symm_apply g)
      rw [this]
      exact hg)

theorem finrank_irr_eq_vendor (X Y : S.Ind) :
    Module.finrank k (S.Irr X Y) = Module.finrank k (S.vendorIrr X Y) :=
  (S.irrEquivVendor X Y).finrank_eq

end Noetherian

end IndSkeleton

end MultiplicativeBasisDeformations
