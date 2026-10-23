module

public import MultiplicativeBasisDeformations.Foundations.A0RepFinite

/-!
# Representation-finiteness of the opposite algebra

The `k`-dual `D = Hom_k(-, k)` sends finite-dimensional left `B`-modules to right `B`-modules,
reverses endomorphism rings and is involutive up to the evaluation isomorphism. Hence a
finite-dimensional algebra is representation-finite if and only if its opposite is
(`isRepresentationFinite_op`). This is used for the dual halves of the local arguments of
Part III ("the dual assertion holds", "passing to the opposite algebra").
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

namespace KDual

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- The action of an element as a `k`-linear map. -/
def lact (M : ModuleCat.{u} B) (b : B) : M →ₗ[k] M where
  toFun m := b • m
  map_add' := smul_add b
  map_smul' c m := by
    change b • (algebraMap k B c • m) = algebraMap k B c • (b • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

theorem lact_apply (M : ModuleCat.{u} B) (b : B) (m : M) : lact (k := k) M b m = b • m := rfl

/-- The right action on the dual. -/
def ρD (M : ModuleCat.{u} B) : Bᵐᵒᵖ →+* Module.End k (Module.Dual k M) where
  toFun b := (lact M b.unop).dualMap
  map_one' := by ext φ m; simp [lact_apply]
  map_mul' a b := by ext φ m; simp [lact_apply, mul_smul]
  map_zero' := by ext φ m; simp [lact_apply]
  map_add' a b := by ext φ m; simp [lact_apply, add_smul]

variable (k) in
/-- The dual space, with the right action of `B`. -/
def DT (M : ModuleCat.{u} B) : Type u := Module.Dual k M

instance (M : ModuleCat.{u} B) : AddCommGroup (DT k M) :=
  inferInstanceAs (AddCommGroup (Module.Dual k M))

instance (M : ModuleCat.{u} B) : Module Bᵐᵒᵖ (DT k M) :=
  Module.compHom (Module.Dual k M) (ρD (k := k) M)

/-- **The dual module.** -/
def D (M : ModuleCat.{u} B) : ModuleCat.{u} Bᵐᵒᵖ := ModuleCat.of Bᵐᵒᵖ (DT k M)

/-- An element of the dual module as a functional. -/
def ofD {M : ModuleCat.{u} B} (φ : D (k := k) M) : Module.Dual k M := φ

/-- A functional as an element of the dual module. -/
def toD {M : ModuleCat.{u} B} (φ : Module.Dual k M) : D (k := k) M := φ

@[simp] theorem ofD_toD {M : ModuleCat.{u} B} (φ : Module.Dual k M) : ofD (toD φ) = φ := rfl

@[simp] theorem toD_ofD {M : ModuleCat.{u} B} (φ : D (k := k) M) : toD (ofD φ) = φ := rfl

theorem D_smul (M : ModuleCat.{u} B) (b : Bᵐᵒᵖ) (φ : D (k := k) M) (m : M) :
    ofD (b • φ) m = ofD φ (b.unop • m) := rfl

theorem ofD_add {M : ModuleCat.{u} B} (φ ψ : D (k := k) M) : ofD (φ + ψ) = ofD φ + ofD ψ := rfl

theorem ofD_zero {M : ModuleCat.{u} B} : ofD (0 : D (k := k) M) = 0 := rfl

/-- The scalar action of `k` on the dual module is the usual one. -/
theorem ofD_smul_k {M : ModuleCat.{u} B} (c : k) (φ : D (k := k) M) : ofD (c • φ) = c • ofD φ := by
  ext m
  change ofD φ (c • m) = c * ofD φ m
  rw [map_smul, smul_eq_mul]

/-- The dual module is the dual space, `k`-linearly. -/
def ofDL (M : ModuleCat.{u} B) : D (k := k) M ≃ₗ[k] Module.Dual k M where
  toFun := ofD
  invFun := toD
  map_add' := ofD_add
  map_smul' := ofD_smul_k
  left_inv _ := rfl
  right_inv _ := rfl

instance (M : ModuleCat.{u} B) [Module.Finite k M] : Module.Finite k (D (k := k) M) :=
  Module.Finite.equiv (ofDL M).symm

/-- A module map as a `k`-linear map. -/
def fk {M N : ModuleCat.{u} B} (f : M ⟶ N) : M →ₗ[k] N where
  toFun := f
  map_add' := map_add f.hom
  map_smul' c m := f.hom.map_smul (algebraMap k B c) m

theorem fk_apply {M N : ModuleCat.{u} B} (f : M ⟶ N) (m : M) : fk (k := k) f m = f m := rfl

/-- The transpose of a module map. -/
def dualHom {M N : ModuleCat.{u} B} (f : M ⟶ N) : DT k N →ₗ[Bᵐᵒᵖ] DT k M where
  toFun φ := toD (ofD φ ∘ₗ fk f)
  map_add' φ ψ := rfl
  map_smul' b φ := by
    apply (ofDL (k := k) M).injective
    ext m
    change ofD φ (b.unop • f m) = ofD φ (f (b.unop • m))
    rw [show f (b.unop • m) = b.unop • f m from f.hom.map_smul _ _]

/-- **The dual of a module map.** -/
def Dmap {M N : ModuleCat.{u} B} (f : M ⟶ N) : D (k := k) N ⟶ D (k := k) M :=
  ModuleCat.ofHom (dualHom f)

theorem Dmap_apply {M N : ModuleCat.{u} B} (f : M ⟶ N) (φ : D (k := k) N) (m : M) :
    ofD (Dmap f φ) m = ofD φ (f m) := rfl

theorem Dmap_comp {M N P : ModuleCat.{u} B} (f : M ⟶ N) (g : N ⟶ P) :
    Dmap (k := k) (f ≫ g) = Dmap g ≫ Dmap f := rfl

theorem Dmap_id (M : ModuleCat.{u} B) : Dmap (k := k) (𝟙 M) = 𝟙 (D M) := rfl

theorem Dmap_add {M N : ModuleCat.{u} B} (f g : M ⟶ N) :
    Dmap (k := k) (f + g) = Dmap f + Dmap g := by
  ext φ
  apply (ofDL (k := k) M).injective
  ext m
  change ofD φ ((f + g).hom m) = ofD φ (f.hom m) + ofD φ (g.hom m)
  rw [ModuleCat.hom_add, LinearMap.add_apply, map_add]

theorem Dmap_zero {M N : ModuleCat.{u} B} : Dmap (k := k) (0 : M ⟶ N) = 0 := by
  ext φ
  apply (ofDL (k := k) M).injective
  ext m
  change ofD φ ((0 : M ⟶ N).hom m) = 0
  rw [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

/-- **Transposition reverses endomorphism rings.** -/
def endD (M : ModuleCat.{u} B) : (End M)ᵐᵒᵖ →+* End (D (k := k) M) where
  toFun f := Dmap f.unop
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := Dmap_zero
  map_add' f g := Dmap_add _ _

theorem endD_injective (M : ModuleCat.{u} B) : Function.Injective (endD (k := k) M) := by
  intro f g h
  apply MulOpposite.unop_injective
  apply ModuleCat.hom_ext
  ext m
  have : ∀ φ : Module.Dual k M, φ (f.unop.hom m - g.unop.hom m) = 0 := fun φ ↦ by
    have := congrArg (fun F : End (D (k := k) M) ↦ ofD (F.hom (toD φ)) m) h
    change φ (f.unop.hom m) = φ (g.unop.hom m) at this
    rw [map_sub]
    exact sub_eq_zero.2 this
  exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff k _).1 this)

section Finite

variable (M : ModuleCat.{u} B) [Module.Finite k M]

/-- The functional on the dual given by an endomorphism of the dual module. -/
def psiE (h : End (D (k := k) M)) (m : M) : Module.Dual k (Module.Dual k M) where
  toFun φ := ofD (h.hom (toD φ)) m
  map_add' φ ψ := by
    change ofD (h.hom (toD φ + toD ψ)) m = _
    rw [map_add]; rfl
  map_smul' c φ := by
    change ofD (h.hom (toD (c • φ))) m = c • ofD (h.hom (toD φ)) m
    rw [show toD (k := k) (c • φ) = (MulOpposite.op (algebraMap k B c)) • toD φ by
      apply (ofDL (k := k) M).injective; ext m'
      change c * φ m' = φ (algebraMap k B c • m')
      rw [← smul_eq_mul, ← map_smul]; rfl]
    rw [map_smul]
    change ofD (h.hom (toD φ)) (algebraMap k B c • m) = c • ofD (h.hom (toD φ)) m
    rw [← map_smul]; rfl

/-- The preimage of an endomorphism of the dual module. -/
def preE (h : End (D (k := k) M)) (m : M) : M := (Module.evalEquiv k M).symm (psiE M h m)

theorem dual_preE (h : End (D (k := k) M)) (m : M) (φ : Module.Dual k M) :
    φ (preE M h m) = ofD (h.hom (toD φ)) m := by
  have := congrArg (fun x ↦ x φ) ((Module.evalEquiv k M).apply_symm_apply (psiE M h m))
  simpa [preE, psiE] using this

theorem eq_of_dual {x y : M} (h : ∀ φ : Module.Dual k M, φ x = φ y) : x = y := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun φ ↦ ?_
  rw [map_sub, h, sub_self]

/-- The preimage as a module map. -/
def preHom (h : End (D (k := k) M)) : M →ₗ[B] M where
  toFun := preE M h
  map_add' m m' := eq_of_dual (k := k) M fun φ ↦ by
    rw [dual_preE, map_add, map_add φ, dual_preE, dual_preE]
  map_smul' b m := eq_of_dual (k := k) M fun φ ↦ by
    rw [dual_preE, RingHom.id_apply]
    have e1 : ofD (h.hom (toD φ)) (b • m) = ofD (MulOpposite.op b • h.hom (toD φ)) m := rfl
    rw [e1, ← map_smul]
    have e2 : MulOpposite.op b • toD (k := k) φ = toD (φ ∘ₗ lact M b) := by
      apply (ofDL (k := k) M).injective; ext m'; rfl
    rw [e2, ← dual_preE]
    rfl

theorem endD_surjective : Function.Surjective (endD (k := k) M) := by
  intro h
  refine ⟨MulOpposite.op (ModuleCat.ofHom (preHom M h)), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (ofDL (k := k) M).injective
  ext m
  change ofD φ (preE M h m) = ofD (h.hom φ) m
  exact dual_preE M h m (ofD φ)

/-- **Transposition is an anti-isomorphism of endomorphism rings.** -/
def endDEquiv : (End M)ᵐᵒᵖ ≃+* End (D (k := k) M) :=
  RingEquiv.ofBijective (endD M) ⟨endD_injective M, endD_surjective M⟩

end Finite

/-- The opposite of a local ring is local. -/
theorem isLocalRing_mop {R : Type*} [Ring R] [IsLocalRing R] : IsLocalRing Rᵐᵒᵖ := by
  haveI : Nontrivial Rᵐᵒᵖ := MulOpposite.unop_injective.nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (R := R) (a := a.unop) (b := 1 - a.unop)
    (by abel) with h | h
  · exact Or.inl (isUnit_op.2 h)
  · exact Or.inr (isUnit_op.2 (by simpa using h))

section DoubleDual

variable [FiniteDimensional k B] (M : ModuleCat.{u} B) [Module.Finite k M]

/-- Evaluation into the double dual. -/
def evD (m : M) : DT k (D (k := k) M) where
  toFun φ := ofD φ m
  map_add' _ _ := rfl
  map_smul' c φ := by rw [ofD_smul_k]; rfl

theorem ofD_evD (m : M) (φ : D (k := k) M) : ofD (evD M m) φ = ofD φ m := rfl

/-- Elements of the restricted module. -/
def toM (m : (toOpOp (A := B)).functor.obj M) : M := m

theorem toM_add (m m' : (toOpOp (A := B)).functor.obj M) : toM M (m + m') = toM M m + toM M m' :=
  rfl

/-- **The double dual**, as a map of right `Bᵒᵖ`-modules. -/
def ddMap : (toOpOp (A := B)).functor.obj M →ₗ[Bᵐᵒᵖᵐᵒᵖ] DT k (D (k := k) M) where
  toFun m := evD M (toM M m)
  map_add' m m' := by
    apply (ofDL (k := k) (D (k := k) M)).injective; ext φ
    change ofD φ (toM M (m + m')) = ofD φ (toM M m) + ofD φ (toM M m')
    rw [toM_add, map_add]
  map_smul' x m := by
    apply (ofDL (k := k) (D (k := k) M)).injective; ext φ
    rfl

theorem ddMap_bijective : Function.Bijective (ddMap (k := k) M) := by
  constructor
  · intro m m' h
    have : toM M m = toM M m' := eq_of_dual (k := k) M fun φ ↦ by
      have := congrArg (fun Ψ ↦ ofD Ψ (toD φ)) h
      exact this
    exact this
  · intro Ψ
    set X := (ofDL (k := k) (D (k := k) M) Ψ).comp (ofDL (k := k) M).symm.toLinearMap
    refine ⟨(Module.evalEquiv k M).symm X, ?_⟩
    apply (ofDL (k := k) (D (k := k) M)).injective; ext φ
    have := congrArg (fun x ↦ x (ofD φ)) ((Module.evalEquiv k M).apply_symm_apply X)
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply] at this
    exact this

/-- **The double dual isomorphism.** -/
def ddIso : (toOpOp (A := B)).functor.obj M ≅ D (k := k) (D (k := k) M) :=
  (LinearEquiv.ofBijective (ddMap (k := k) M) (ddMap_bijective M)).toModuleIso

end DoubleDual

/-- The dual of an isomorphism. -/
def Diso {M N : ModuleCat.{u} B} (e : M ≅ N) : D (k := k) N ≅ D (k := k) M where
  hom := Dmap e.hom
  inv := Dmap e.inv
  hom_inv_id := by rw [← Dmap_comp, e.inv_hom_id, Dmap_id]
  inv_hom_id := by rw [← Dmap_comp, e.hom_inv_id, Dmap_id]

end KDual

open KDual in
/-- **The opposite of a representation-finite algebra is representation-finite.** -/
theorem isRepresentationFinite_op {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]
    [FiniteDimensional k B] (hB : IsRepresentationFinite k B) : IsRepresentationFinite k Bᵐᵒᵖ := by
  classical
  obtain ⟨n, Y, hY, hcov⟩ := hB
  have hlocY : ∀ i, IsLocalRing (End (Y i)) := fun i ↦ by
    haveI := (hY i).1
    exact MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Bᵐᵒᵖ) (Y i) (hY i).2
  refine isRepresentationFinite_op_of_left (k := k)
    (fun i ↦ (toOpOp (A := B)).inverse.obj (D (k := k) (Y i))) (fun i ↦ ⟨?_, ?_⟩) ?_
  · haveI := (hY i).1
    exact Module.Finite.of_surjective (ofOpOpK (k := k) (D (k := k) (Y i))) fun m ↦ ⟨m, rfl⟩
  · haveI := (hY i).1
    haveI := hlocY i
    haveI : IsLocalRing (End (Y i))ᵐᵒᵖ := isLocalRing_mop
    haveI : IsLocalRing (End (D (k := k) (Y i))) :=
      MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm (endDEquiv (k := k) (Y i))
    exact MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
      (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful
        (toOpOp (A := B)).inverse (D (k := k) (Y i)))
  · intro M hMf hM
    haveI := hMf
    haveI : IsLocalRing (End M) :=
      MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := B) M hM
    haveI : IsLocalRing (End M)ᵐᵒᵖ := isLocalRing_mop
    haveI : IsLocalRing (End (D (k := k) M)) :=
      MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm (endDEquiv (k := k) M)
    obtain ⟨i, ⟨e⟩⟩ := hcov (D (k := k) M) ⟨inferInstance,
      MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _⟩
    exact ⟨i, ⟨(toOpOp (A := B)).unitIso.app M ≪≫
      (toOpOp (A := B)).inverse.mapIso (ddIso (k := k) M ≪≫ (Diso (k := k) e).symm)⟩⟩


end MultiplicativeBasisDeformations
