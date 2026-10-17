import MultiplicativeBasisDeformations.Foundations.InjectiveLabels
import MultiplicativeBasisDeformations.Foundations.Exchange
import MultiplicativeBasisDeformations.Foundations.Twist
import MultiplicativeBasisDeformations.Foundations.CategoryAlgebraCorners

/-!
# Proposition 2.10(2): `A₀` is representation-finite

`prop:projective-evaluation`(2) (`graded-category.tex`): evaluation
`add C → mod A₀` is an equivalence, so the indecomposable `A₀`-modules are the
evaluations of the finitely many objects of `C`.

Every finite-dimensional module is the evaluation of a family
(`InjData.essSurj`); an indecomposable one has local endomorphism ring and is a
retract of one summand (exchange), which is an evaluation `R_x` with local
endomorphism ring `C(x, x)` (full faithfulness), hence isomorphic to it.
Modules of `Alg F₀` are the paper's right `A₀`-modules; they are transported to
right modules of `(Alg F₀)ᵒᵖ` along `R ≅ Rᵒᵖᵒᵖ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v w

/-! ### Left modules versus right modules of the opposite algebra -/

section Op

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Left `A`-modules as right `Aᵒᵖ`-modules. -/
def toOpOp : ModuleCat.{v} A ≌ RightModuleCat Aᵐᵒᵖ :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A).symm

instance : (toOpOp (A := A)).functor.Additive :=
  inferInstanceAs (ModuleCat.restrictScalars _).Additive
instance : (toOpOp (A := A)).inverse.Additive := by
  change (ModuleCat.restrictScalars _).Additive; infer_instance

/-- The identity map is `k`-linear for the induced structures. -/
def toOpOpK (M : ModuleCat.{v} A) : M →ₗ[k] (toOpOp (A := A)).functor.obj M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := by
    change algebraMap k A c • m = (RingEquiv.opOp A).symm (algebraMap k Aᵐᵒᵖᵐᵒᵖ c) • m
    rfl

/-- And back. -/
def ofOpOpK (N : RightModuleCat Aᵐᵒᵖ) : N →ₗ[k] (toOpOp (A := A)).inverse.obj N where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := by
    change algebraMap k Aᵐᵒᵖᵐᵒᵖ c • m = (RingEquiv.opOp A) (algebraMap k A c) • m
    rfl

/-- Representation-finiteness of `Aᵒᵖ` from a finite list of left
`A`-modules. -/
theorem isRepresentationFinite_op_of_left {n : ℕ} (X : Fin n → ModuleCat.{v} A)
    (hX : ∀ i, Module.Finite k (X i) ∧ IsLocalRing (End (X i)))
    (hcov : ∀ M : ModuleCat.{v} A, Module.Finite k M → Indecomposable M →
      ∃ i, Nonempty (M ≅ X i)) :
    IsRepresentationFinite k Aᵐᵒᵖ := by
  haveI : Module.Finite k Aᵐᵒᵖ := inferInstance
  haveI : Module.Finite k Aᵐᵒᵖᵐᵒᵖ := inferInstance
  refine ⟨n, fun i ↦ (toOpOp (A := A)).functor.obj (X i), fun i ↦ ?_, fun N hN ↦ ?_⟩
  · haveI := (hX i).1
    haveI := (hX i).2
    have hloc : IsLocalRing (End ((toOpOp (A := A)).functor.obj (X i))) :=
      MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
        (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful
          (toOpOp (A := A)).functor (X i))
    exact ⟨Module.Finite.of_surjective (toOpOpK (k := k) (X i)) fun m ↦ ⟨m, rfl⟩,
      @MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _ _ _ _ _ hloc⟩
  · haveI := hN.1
    haveI : IsLocalRing (End N) :=
      MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Aᵐᵒᵖᵐᵒᵖ) N hN.2
    have hloc : IsLocalRing (End ((toOpOp (A := A)).inverse.obj N)) :=
      MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
        (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful
          (toOpOp (A := A)).inverse N)
    haveI : Module.Finite k ((toOpOp (A := A)).inverse.obj N) :=
      Module.Finite.of_surjective (ofOpOpK (k := k) N) fun m ↦ ⟨m, rfl⟩
    obtain ⟨i, ⟨e⟩⟩ := hcov _ inferInstance
      (@MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _ _ _ _ _ hloc)
    exact ⟨i, ⟨((toOpOp (A := A)).counitIso.app N).symm ≪≫
      (toOpOp (A := A)).functor.mapIso e⟩⟩

end Op

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}
  {L : LocalFamily (k := k) F} (D : MeshData F L)

/-- **Endomorphism rings in a local family are local.** -/
theorem LocalFamily.end_isLocalRing (L : LocalFamily (k := k) F) (x : ι) :
    IsLocalRing (End (F x)) := by
  haveI : Nontrivial (End (F x)) := ⟨⟨𝟙 _, 0, fun h ↦ L.id_not_mem x (by
    change (𝟙 (F x) : F x ⟶ F x) ∈ L.rad x x
    rw [show (𝟙 (F x) : F x ⟶ F x) = 0 from h]; exact Submodule.zero_mem _)⟩⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  obtain ⟨c, hc⟩ := L.diag x f
  have hnil := L.nilpotent x _ hc
  by_cases h0 : c = 0
  · right
    rw [h0, zero_smul, sub_zero] at hc
    exact (L.nilpotent x f hc).isUnit_one_sub
  · left
    have hu : IsUnit (algebraMap k (End (F x)) c) := (Ne.isUnit h0).map _
    let r : End (F x) := (show F x ⟶ F x from f) - c • 𝟙 (F x)
    have hr : IsNilpotent r := hnil
    have hcomm : Commute r (algebraMap k (End (F x)) c) := (Algebra.commutes c _).symm
    have := hr.isUnit_add_left_of_commute hu hcomm
    rw [Algebra.algebraMap_eq_smul_one] at this
    have e : c • (1 : End (F x)) + r = f := by
      change c • 𝟙 (F x) + ((show F x ⟶ F x from f) - c • 𝟙 (F x)) = f
      abel
    rwa [e] at this

namespace MeshData

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] {D}

instance : FiniteDimensional k (Alg D.F0) := finiteDimensional_alg

instance (x : ι) : FiniteDimensional k (Rep D.F0 (F x)) :=
  inferInstanceAs (FiniteDimensional k (∀ p : D.PV, F p.1 ⟶ F x))

/-- The evaluation `R⁰_x` of a label as a module. -/
def evObj (x : ι) : ModuleCat (Alg D.F0) := ModuleCat.of (Alg D.F0) (Rep D.F0 (F x))

/-- The identity of `R⁰_x` from the native `k`-structure. -/
def evObjK (x : ι) : Rep D.F0 (F x) →ₗ[k] evObj (D := D) x where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := by
    change c • m = algebraMap k (Alg D.F0) c • m
    exact (algebraMap_smul (Alg D.F0) c m).symm

instance evObj_finite (x : ι) : Module.Finite k (evObj (D := D) x) :=
  Module.Finite.of_surjective (evObjK x) fun m ↦ ⟨m, rfl⟩

/-- The evaluation of an endomorphism. -/
def evHom {x : ι} (f : F x ⟶ F x) : evObj (D := D) x ⟶ evObj (D := D) x :=
  ModuleCat.ofHom (repMap (F := D.F0) f)

theorem evHom_apply {x : ι} (f : F x ⟶ F x) (m : Rep D.F0 (F x)) :
    (evHom (D := D) f).hom m = repMap (F := D.F0) f m := rfl

/-- Endomorphisms of an evaluation are evaluations of endomorphisms. -/
def evEndHom (x : ι) : End (F x) →+* End (evObj (D := D) x) where
  toFun f := evHom (D := D) f
  map_one' := ModuleCat.hom_ext (LinearMap.ext fun m ↦ by
    change repMap (F := D.F0) (𝟙 (F x)) m = m
    exact funext fun y ↦ Category.comp_id _)
  map_mul' f g := ModuleCat.hom_ext (LinearMap.ext fun m ↦ by
    change repMap (F := D.F0) (g ≫ f) m = repMap (F := D.F0) f (repMap (F := D.F0) g m)
    rw [repMap_comp]; rfl)
  map_zero' := ModuleCat.hom_ext (LinearMap.ext fun m ↦ by
    change repMap (F := D.F0) (0 : F x ⟶ F x) m = 0
    rw [repMap_zero]; rfl)
  map_add' f g := ModuleCat.hom_ext (LinearMap.ext fun m ↦ by
    change repMap (F := D.F0) (f + g : F x ⟶ F x) m =
      repMap (F := D.F0) f m + repMap (F := D.F0) g m
    rw [repMap_add]; rfl)

include hfd in
theorem evEndHom_bijective (x : ι) : Function.Bijective (evEndHom (D := D) x) := by
  constructor
  · intro f g h
    have h' : ∀ m, repMap (F := D.F0) ((f : F x ⟶ F x) - (g : F x ⟶ F x)) m = 0 := fun m ↦ by
      have := congrArg (fun φ : End (evObj (D := D) x) ↦ φ.hom m) h
      change repMap (F := D.F0) (f : F x ⟶ F x) m = repMap (F := D.F0) (g : F x ⟶ F x) m at this
      funext y
      have hy := congrFun this y
      rw [repMap_apply, repMap_apply] at hy
      rw [repMap_apply, Preadditive.comp_sub, hy, sub_self]; rfl
    exact sub_eq_zero.1 (D.repMap_eq_zero x x _ h')
  · intro φ
    obtain ⟨h, hh⟩ := D.hom_eq_repMap x x φ.hom
    exact ⟨h, ModuleCat.hom_ext (LinearMap.ext fun m ↦ (hh m).symm)⟩

include hfd in
theorem evObj_isLocalRing (x : ι) : IsLocalRing (End (evObj (D := D) x)) := by
  have := L.end_isLocalRing x
  exact MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
    (RingEquiv.ofBijective (evEndHom (D := D) x) (evEndHom_bijective x))

variable (J : InjData D)

include J in
/-- Every finite-dimensional indecomposable `A₀`-module is the evaluation of a
label. -/
theorem exists_iso_evObj (M : ModuleCat.{w} (Alg D.F0)) [Module.Finite k M]
    (hM : Indecomposable M) : ∃ x : ι, Nonempty (M ≅ evObj (D := D) x) := by
  have : IsLocalRing (End M) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Alg D.F0) M hM
  obtain ⟨μ, _, _, W, ⟨e⟩⟩ := J.essSurj (X := M)
  let Y : μ → ModuleCat.{w} (Alg D.F0) := fun j ↦ evObj (D := D) (W j)
  let φ : M ≅ ⨁ Y := e.toModuleIso ≪≫ (ModuleCat.biproductIsoPi Y).symm
  obtain ⟨j, i', p', h⟩ := exists_retract_summand Y φ.hom φ.inv φ.hom_inv_id
  have := evObj_isLocalRing (D := D) (W j)
  have := isIso_of_retract hM.1 i' p' h
  exact ⟨W j, ⟨asIso i'⟩⟩

include J in
/-- **Proposition 2.10(2)**: `A₀` is representation-finite. -/
theorem isRepresentationFinite_A0 : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ := by
  classical
  let eι := Fintype.equivFin ι
  refine isRepresentationFinite_op_of_left (fun i ↦ evObj (D := D) (eι.symm i))
    (fun i ↦ ⟨evObj_finite _, evObj_isLocalRing _⟩) fun M hMf hM ↦ ?_
  obtain ⟨x, ⟨e⟩⟩ := exists_iso_evObj J M hM
  exact ⟨eι x, ⟨e ≪≫ eqToIso (by rw [Equiv.symm_apply_apply])⟩⟩

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
