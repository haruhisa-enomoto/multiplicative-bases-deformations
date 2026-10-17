import MBDVendor.Magnitude.Algebra.FiniteModuleDecomposition
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Representation-finite algebras and finite right-module skeletons

Finitely generated right `A`-modules are represented using Mathlib's left
module category over `Aᵐᵒᵖ`.  Representation-finiteness is the finiteness of
the isomorphism classes of finite-dimensional indecomposable right modules.

The skeleton construction is adapted from
`CartanDeterminant.Algebra.RepresentationFinite` and
`CartanDeterminant.RepresentationTheory.FiniteIndecomposableSkeleton` at
homological-conjectures commit `eade4e75`, with the module side made explicit
and the unrelated Auslander-algebra layer omitted.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule

universe u v

variable (k : Type u) [Field k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- Mathlib model for right `A`-modules: left modules over `Aᵐᵒᵖ`. -/
abbrev Category := ModuleCat.{v} Aᵐᵒᵖ

/-- A finite-dimensional indecomposable right `A`-module. -/
def IsFiniteIndecomposable (M : Category A) : Prop :=
  Module.Finite k M ∧ Indecomposable M

/-- There are finitely many isomorphism classes of finite-dimensional
indecomposable right `A`-modules.  The witnessing family may contain
repetitions. -/
def IsRepresentationFinite : Prop :=
  ∃ n : ℕ, ∃ X : Fin n → Category A,
    (∀ i, IsFiniteIndecomposable k A (X i)) ∧
      ∀ M : Category A, IsFiniteIndecomposable k A M →
        ∃ i, Nonempty (M ≅ X i)

/-- Mathlib's literal category of finitely generated right `A`-modules. -/
abbrev FinitelyGeneratedCategory := FGModuleCat.{v} Aᵐᵒᵖ

/-- Representation-finiteness stated literally on finitely generated right
modules.  Indecomposability is tested after the fully faithful inclusion into
the ambient module category. -/
def IsRepresentationFiniteFinitelyGenerated : Prop :=
  ∃ n : ℕ, ∃ X : Fin n → FinitelyGeneratedCategory A,
    (∀ i, Indecomposable (X i).obj) ∧
      ∀ M : FinitelyGeneratedCategory A, Indecomposable M.obj →
        ∃ i, Nonempty (M ≅ X i)

/-- A finitely generated right module over a finite-dimensional algebra is
finite-dimensional over the coefficient field. -/
theorem finite_over_field_of_finitelyGenerated
    [FiniteDimensional k A] (M : FinitelyGeneratedCategory A) :
    Module.Finite k M := by
  exact Module.Finite.trans Aᵐᵒᵖ M

/-- A finite-dimensional right module is finitely generated over `Aᵐᵒᵖ`. -/
def finitelyGeneratedOfFiniteDimensional
    (M : Category A) [Module.Finite k M] : FinitelyGeneratedCategory A :=
  ⟨M, Module.Finite.of_restrictScalars_finite k Aᵐᵒᵖ M⟩

/-- For a finite-dimensional algebra, the finite-dimensional and literally
finitely generated formulations of right representation-finiteness agree. -/
theorem isRepresentationFinite_iff_finitelyGenerated
    [FiniteDimensional k A] :
    IsRepresentationFinite k A ↔
      IsRepresentationFiniteFinitelyGenerated A := by
  constructor
  · rintro ⟨n, X, hX, hcover⟩
    let Xfg : Fin n → FinitelyGeneratedCategory A := fun i ↦
      @finitelyGeneratedOfFiniteDimensional k _ A _ _ (X i) (hX i).1
    refine ⟨n, Xfg, fun i ↦ (hX i).2, ?_⟩
    intro M hM
    letI : Module.Finite k M := finite_over_field_of_finitelyGenerated k A M
    obtain ⟨i, ⟨e⟩⟩ := hcover M.obj ⟨inferInstance, hM⟩
    exact ⟨i, ⟨ObjectProperty.isoMk _ e⟩⟩
  · rintro ⟨n, X, hX, hcover⟩
    refine ⟨n, fun i ↦ (X i).obj, ?_, ?_⟩
    · intro i
      exact ⟨finite_over_field_of_finitelyGenerated k A (X i), hX i⟩
    · intro M hM
      let Mfg : FinitelyGeneratedCategory A :=
        @finitelyGeneratedOfFiniteDimensional k _ A _ _ M hM.1
      obtain ⟨i, ⟨e⟩⟩ := hcover Mfg hM.2
      exact ⟨i, ⟨(forget₂ (FinitelyGeneratedCategory A) (Category A)).mapIso e⟩⟩

/-- A finite skeleton of the finite-dimensional indecomposable right
`A`-modules. -/
structure FiniteIndecomposableSkeleton where
  n : ℕ
  obj : Fin n → Category A
  obj_finite : ∀ i, Module.Finite k (obj i)
  obj_indecomposable : ∀ i, Indecomposable (obj i)
  eq_of_iso : ∀ {i j}, Nonempty (obj i ≅ obj j) → i = j
  complete : ∀ M : Category A,
    IsFiniteIndecomposable k A M → ∃ i, Nonempty (M ≅ obj i)

namespace FiniteIndecomposableSkeleton

variable {k A}

/-- Isomorphism of modules in a family is an equivalence relation on its
index type. -/
def moduleIsoSetoid {σ : Type*} (X : σ → Category A) : Setoid σ where
  r i j := Nonempty (X i ≅ X j)
  iseqv := {
    refl := fun i ↦ ⟨Iso.refl (X i)⟩
    symm := fun h ↦ h.map Iso.symm
    trans := fun hij hjl ↦ Nonempty.map2 Iso.trans hij hjl }

/-- Representation-finiteness supplies an actual finite skeleton with no
repeated isomorphism classes. -/
theorem exists_of_isRepresentationFinite
    (hA : IsRepresentationFinite k A) :
    Nonempty (FiniteIndecomposableSkeleton k A) := by
  obtain ⟨n, X, hX, hcover⟩ := hA
  let s : Setoid (Fin n) := moduleIsoSetoid X
  letI : DecidableRel ((· ≈ ·) : Fin n → Fin n → Prop) :=
    Classical.decRel _
  letI : Fintype (Quotient s) := Quotient.fintype s
  let e : Quotient s ≃ Fin (Fintype.card (Quotient s)) :=
    Fintype.equivFin (Quotient s)
  let Y : Fin (Fintype.card (Quotient s)) → Category A :=
    fun i ↦ X (e.symm i).out
  refine ⟨{
    n := Fintype.card (Quotient s)
    obj := Y
    obj_finite := ?_
    obj_indecomposable := ?_
    eq_of_iso := ?_
    complete := ?_ }⟩
  · intro i
    exact (hX (e.symm i).out).1
  · intro i
    exact (hX (e.symm i).out).2
  · intro i j hij
    apply e.symm.injective
    apply Quotient.out_equiv_out.mp
    exact hij
  · intro M hM
    obtain ⟨i, ⟨hMi⟩⟩ := hcover M hM
    let q : Quotient s := Quotient.mk'' i
    let j := e q
    have hq : e.symm j = q := e.symm_apply_apply q
    have hout : (e.symm j).out ≈ i := by
      apply Quotient.exact
      rw [hq, Quotient.out_eq]
    obtain ⟨houtIso⟩ := hout
    exact ⟨j, ⟨hMi.trans houtIso.symm⟩⟩

variable (S : FiniteIndecomposableSkeleton k A)

/-- Every finite-dimensional right module is a finite biproduct of objects
from the chosen duplicate-free indecomposable skeleton. -/
theorem obj_decomposition [FiniteDimensional k A]
    (M : Category A) [Module.Finite k M] :
    ∃ n : ℕ, ∃ label : Fin n → Fin S.n,
      Nonempty (M ≅ ⨁ fun i ↦ S.obj (label i)) := by
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_module_exists
    (k := k) M
  have hcomplete (j : Fin d.n) :
      ∃ i, Nonempty (d.summand j ≅ S.obj i) :=
    S.complete (d.summand j)
      ⟨d.summand_finite (k := k) inferInstance j, d.indecomposable j⟩
  choose label hlabel using hcomplete
  exact ⟨d.n, label, ⟨d.isoBiproduct.trans
    (biproduct.mapIso fun j ↦ Classical.choice (hlabel j))⟩⟩

/-- A chosen finite-dimensional skeleton object, bundled as a finitely
generated right module. -/
def fgObj (i : Fin S.n) : FinitelyGeneratedCategory A :=
  @finitelyGeneratedOfFiniteDimensional k _ A _ _ (S.obj i) (S.obj_finite i)

/-- Indecomposability of a finitely generated right module is detected by the
fully faithful inclusion into all right modules. -/
theorem indecomposable_iff_obj [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ] (M : FinitelyGeneratedCategory A) :
    Indecomposable M ↔ Indecomposable M.obj := by
  let U := forget₂ (FinitelyGeneratedCategory A) (Category A)
  letI : U.Additive := ⟨by intros; rfl⟩
  constructor
  · intro hM
    refine ⟨?_, ?_⟩
    · intro hzero
      exact hM.1 (IsZero.of_full_of_faithful_of_isZero U M hzero)
    · intro Y Z e
      let pY : M.obj ⟶ Y := e.hom ≫ biprod.fst
      let pZ : M.obj ⟶ Z := e.hom ≫ biprod.snd
      letI : Module.Finite Aᵐᵒᵖ Y :=
        Module.Finite.of_surjective pY.hom
          ((ModuleCat.epi_iff_surjective pY).mp inferInstance)
      letI : Module.Finite Aᵐᵒᵖ Z :=
        Module.Finite.of_surjective pZ.hom
          ((ModuleCat.epi_iff_surjective pZ).mp inferInstance)
      let Yfg : FinitelyGeneratedCategory A :=
        ⟨Y, show Module.Finite Aᵐᵒᵖ Y from inferInstance⟩
      let Zfg : FinitelyGeneratedCategory A :=
        ⟨Z, show Module.Finite Aᵐᵒᵖ Z from inferInstance⟩
      letI : PreservesBinaryBiproduct Yfg Zfg U :=
        preservesBinaryBiproduct_of_preservesBinaryProduct U
      let efg : M ≅ Yfg ⊞ Zfg :=
        ObjectProperty.isoMk _
          (e.trans (U.mapBiprod Yfg Zfg).symm)
      rcases hM.2 Yfg Zfg efg with hY | hZ
      · have hYu := U.map_isZero hY
        change IsZero Y at hYu
        exact Or.inl hYu
      · have hZu := U.map_isZero hZ
        change IsZero Z at hZu
        exact Or.inr hZu
  · intro hM
    refine ⟨?_, ?_⟩
    · intro hzero
      exact hM.1 (U.map_isZero hzero)
    · intro Y Z e
      letI : PreservesBinaryBiproduct Y Z U :=
        preservesBinaryBiproduct_of_preservesBinaryProduct U
      let eUnderlying : M.obj ≅ U.obj Y ⊞ U.obj Z :=
        (U.mapIso e).trans (U.mapBiprod Y Z)
      rcases hM.2 (U.obj Y) (U.obj Z) eUnderlying with hY | hZ
      · exact Or.inl (IsZero.of_full_of_faithful_of_isZero U Y hY)
      · exact Or.inr (IsZero.of_full_of_faithful_of_isZero U Z hZ)

/-- A chosen skeleton object remains indecomposable when bundled as a
finitely generated right module. -/
theorem fgObj_indecomposable [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ] (i : Fin S.n) :
    Indecomposable (S.fgObj i) :=
  (indecomposable_iff_obj (k := k) (A := A) (S.fgObj i)).2
    (S.obj_indecomposable i)

/-- The chosen finitely generated skeleton contains every indecomposable
finitely generated right module. -/
theorem fgObj_complete [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ] (M : FinitelyGeneratedCategory A)
    (hM : Indecomposable M) :
    ∃ i : Fin S.n, Nonempty (M ≅ S.fgObj i) := by
  obtain ⟨i, ⟨e⟩⟩ := S.complete M.obj
    ⟨finite_over_field_of_finitelyGenerated k A M,
      (indecomposable_iff_obj (k := k) (A := A) M).1 hM⟩
  exact ⟨i, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- The chosen finitely generated skeleton has no repeated isomorphism
classes. -/
theorem fgObj_skeletal {i j : Fin S.n}
    (h : Nonempty (S.fgObj i ≅ S.fgObj j)) : i = j := by
  apply S.eq_of_iso
  have hu := h.map (fun e ↦
    (forget₂ (FinitelyGeneratedCategory A) (Category A)).mapIso e)
  change Nonempty (S.obj i ≅ S.obj j) at hu
  exact hu

/-- The opposite of a finite-dimensional algebra is Noetherian, so its
finitely generated module category is abelian and idempotent-complete.  This
is a named value rather than a global instance because the coefficient field
is not determined by the target ring. -/
theorem oppositeIsNoetherian [FiniteDimensional k A] :
    IsNoetherianRing Aᵐᵒᵖ :=
  IsNoetherianRing.of_finite k Aᵐᵒᵖ

/-- Every finitely generated right module over a finite-dimensional algebra
is a finite biproduct of the chosen skeleton objects, now inside the literal
finitely generated module category. -/
theorem fgObj_decomposition [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ] (M : FinitelyGeneratedCategory A) :
    ∃ n : ℕ, ∃ label : Fin n → Fin S.n,
      Nonempty (M ≅ ⨁ fun i ↦ S.fgObj (label i)) := by
  letI : Module.Finite k M := finite_over_field_of_finitelyGenerated k A M
  obtain ⟨n, label, ⟨e⟩⟩ := S.obj_decomposition (k := k) M.obj
  let U := forget₂ (FinitelyGeneratedCategory A) (Category A)
  letI : PreservesBiproduct (fun i ↦ S.fgObj (label i)) U :=
    preservesBiproduct_of_preservesProduct U
  let eUnderlying : M.obj ≅
      U.obj (⨁ fun i ↦ S.fgObj (label i)) :=
    e.trans (U.mapBiproduct (fun i ↦ S.fgObj (label i))).symm
  exact ⟨n, label, ⟨ObjectProperty.isoMk _ eUnderlying⟩⟩

/-- The full category on the chosen finite right-module skeleton. -/
abbrev IndecCategory :=
  InducedCategory (Category A) S.obj

noncomputable instance categoryFintype : Fintype S.IndecCategory := by
  change Fintype (Fin S.n)
  infer_instance

/-- The fully faithful inclusion of the finite indecomposable skeleton into
the right-module category. -/
abbrev inclusion : S.IndecCategory ⥤ Category A :=
  inducedFunctor S.obj

instance inclusion_additive : S.inclusion.Additive := by infer_instance

instance inclusion_linear : S.inclusion.Linear k := by infer_instance

/-- Every chosen skeleton object is finite-dimensional over `k`. -/
theorem indecCategory_obj_finite (i : S.IndecCategory) :
    Module.Finite k (S.inclusion.obj i) :=
  S.obj_finite i

/-- Every chosen skeleton object is indecomposable. -/
theorem indecCategory_obj_indecomposable (i : S.IndecCategory) :
    Indecomposable (S.inclusion.obj i) :=
  S.obj_indecomposable i

/-- Hom spaces between finite-dimensional right modules are finite-dimensional
over the coefficient field. -/
theorem moduleCat_hom_finite (M N : Category A)
    [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (M ⟶ N) := by
  let f : (M ⟶ N) →ₗ[k] (M →ₗ[k] N) :=
    (LinearMap.restrictScalarsₗ k Aᵐᵒᵖ M N k).comp
      ModuleCat.homLinearEquiv.toLinearMap
  exact Module.Finite.of_injective f
    ((LinearMap.restrictScalars_injective k).comp
      ModuleCat.homLinearEquiv.injective)

/-- Hom spaces in the literal category of finitely generated right modules
are finite-dimensional over the coefficient field. -/
noncomputable instance fgModuleCatHomFinite [FiniteDimensional k A]
    (M N : FinitelyGeneratedCategory A) :
    Module.Finite k (M ⟶ N) := by
  letI : Module.Finite k M := finite_over_field_of_finitelyGenerated k A M
  letI : Module.Finite k N := finite_over_field_of_finitelyGenerated k A N
  exact (moduleCat_hom_finite (k := k) (A := A) M.obj N.obj).equiv
    InducedCategory.homLinearEquiv.symm

noncomputable instance indecCategoryHomFinite (i j : S.IndecCategory) :
    Module.Finite k (i ⟶ j) := by
  letI : Module.Finite k (S.obj i) := S.obj_finite i
  letI : Module.Finite k (S.obj j) := S.obj_finite j
  exact (moduleCat_hom_finite (k := k) (A := A) (S.obj i) (S.obj j)).equiv
    InducedCategory.homLinearEquiv.symm

/-- Isomorphic objects of the chosen right-module skeleton have equal labels.
-/
theorem indecCategory_eq_of_iso {i j : S.IndecCategory}
    (h : Nonempty (i ≅ j)) : i = j := by
  apply S.eq_of_iso
  exact h.map (fun e ↦ S.inclusion.mapIso e)

end FiniteIndecomposableSkeleton

end MBDVendor.Magnitude.RightModule
