import MultiplicativeBasisDeformations.Refinements.LiftedCorner
import MultiplicativeBasisDeformations.Foundations.A0RepFinite

/-!
# Corollary 12.1: all modules over a positive deformation

`deformation-refinements.tex`: every positive filtered deformation `B` of `A₀` is
representation-finite, and the lifted normalized modules `M_x^B` exhaust its indecomposables.

Formalization. The lifted modules carry mesh data (`meshB`, `LiftedMeshData.lean`) with the
injective labels of `A₀` (`injB`, the dimensions agree with `C` by `finrank_FB`), and their corner
algebra at the projective labels is `B` (`cornerEquiv`, `LiftedCorner.lean`). Proposition 2.10
applied to this mesh data gives representation-finiteness, and every indecomposable is an
evaluated module; the evaluation of `M_x^B` at the regular projectives `φ(e_p) B ≅ M_p^B` is
`M_x^B` itself (`evIso`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {B : Type u} [Ring B] [Algebra k B] {P : PosFiltration (lenA0 D hfin) B}
  (Ls : Lifts D hfin P) (S : Split P)
  (hleft : ∀ i a, S.φ ((vxIdem D hfin).e i * a) = S.φ ((vxIdem D hfin).e i) * S.φ a)
  (Vx : LenGrading.Vertices (lenA0 D hfin))

/-! ### Evaluation at the regular projectives -/

theorem exists_u (p : D.PV) : ∃ m, θ Ls S hleft Vx p m = Ep S p :=
  (mem_range_θ Ls S hleft Vx p (Ep S p)).2 (Ep_idem S hleft p)

/-- The generator `u_p ∈ M_p^B` corresponding to `E_p ∈ E_p B`. -/
def uB (p : D.PV) : Rep D.F0 (meshFam Q c p.1) := (exists_u Ls S hleft Vx p).choose

theorem θ_uB (p : D.PV) : θ Ls S hleft Vx p (uB Ls S hleft Vx p) = Ep S p :=
  (exists_u Ls S hleft Vx p).choose_spec

theorem Ep_θ (p : D.PV) (n) : Ep S p * θ Ls S hleft Vx p n = θ Ls S hleft Vx p n :=
  (mem_range_θ Ls S hleft Vx p _).1 ⟨n, rfl⟩

theorem uB_act_θ (p : D.PV) (n) :
    (Ls.L p.1).act (uB Ls S hleft Vx p) (θ Ls S hleft Vx p n) = n := by
  apply θ_injective Ls S hleft Vx p
  rw [θ_act, θ_uB, Ep_θ]

theorem uB_act_θ_ne {p q : D.PV} (h : p ≠ q) (n) :
    (Ls.L q.1).act (uB Ls S hleft Vx q) (θ Ls S hleft Vx p n) = 0 := by
  apply θ_injective Ls S hleft Vx q
  rw [θ_act, θ_uB, ← Ep_θ Ls S hleft Vx p n, ← mul_assoc, Ep_mul_Ep S hleft, if_neg (Ne.symm h),
    zero_mul, map_zero]

theorem sum_ξ_uB (b : B) (q : D.PV) :
    ∑ p, ξ Ls S hleft Vx b p q (uB Ls S hleft Vx p) = (Ls.L q.1).act (uB Ls S hleft Vx q) b := by
  apply θ_injective Ls S hleft Vx q
  rw [map_sum, θ_act, θ_uB]
  simp only [θ_ξ, θ_uB]
  rw [← Finset.mul_sum, sum_Ep S, mul_one]

variable (x : V)

/-- The evaluation `⊕_p Hom(M_p^B, M_x^B) → M_x^B`, `f ↦ Σ_p f_p(u_p)`. -/
def evB : Rep (fun p : D.PV ↦ FB Ls p.1) (FB Ls x) →ₗ[k] Rep D.F0 (meshFam Q c x) where
  toFun f := ∑ p, toLin (f p) (uB Ls S hleft Vx p)
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ by
      change toLin (f p + g p) _ = _
      rw [toLin_add, LinearMap.add_apply]
  map_smul' t f := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by
      change toLin (t • f p) _ = _
      rw [toLin_smul, LinearMap.smul_apply]; rfl

theorem evB_apply (f : Rep (fun p : D.PV ↦ FB Ls p.1) (FB Ls x)) :
    evB Ls S hleft Vx x f = ∑ p, toLin (f p) (uB Ls S hleft Vx p) := rfl

/-- The inverse: `m ↦ (n ↦ m · θ_p(n))_p`. -/
def evBInv (m : Rep D.F0 (meshFam Q c x)) : Rep (fun p : D.PV ↦ FB Ls p.1) (FB Ls x) :=
  fun p ↦ ofLin Ls ((Ls.L x).act m ∘ₗ θ Ls S hleft Vx p) fun n b ↦ by
    simp only [LinearMap.comp_apply, θ_act, (Ls.L x).mul]

theorem evB_evBInv (m : Rep D.F0 (meshFam Q c x)) :
    evB Ls S hleft Vx x (evBInv Ls S hleft Vx x m) = m := by
  rw [evB_apply]
  simp only [evBInv, toLin_ofLin, LinearMap.comp_apply, θ_uB]
  rw [← map_sum, sum_Ep S, (Ls.L x).one]

theorem evBInv_evB (f : Rep (fun p : D.PV ↦ FB Ls p.1) (FB Ls x)) :
    evBInv Ls S hleft Vx x (evB Ls S hleft Vx x f) = f := by
  refine Rep.ext fun p ↦ toLin_injective (LinearMap.ext fun n ↦ ?_)
  simp only [evBInv, toLin_ofLin, LinearMap.comp_apply, evB_apply, map_sum, LinearMap.sum_apply]
  simp only [← toLin_act]
  rw [Finset.sum_eq_single p]
  · rw [uB_act_θ]
  · intro q _ hq; rw [uB_act_θ_ne Ls S hleft Vx (Ne.symm hq), map_zero]
  · simp

theorem evB_smul (b : B) (f : Rep (fun p : D.PV ↦ FB Ls p.1) (FB Ls x)) :
    evB Ls S hleft Vx x ((Ξ Ls S hleft Vx b).unop • f) =
      (Ls.L x).act (evB Ls S hleft Vx x f) b := by
  rw [evB_apply, evB_apply, map_sum, LinearMap.sum_apply]
  simp only [Rep.smul_apply, toLin_sum, LinearMap.sum_apply, toLin_comp, LinearMap.comp_apply,
    toLin_Ξ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← map_sum, sum_ξ_uB, toLin_act]

/-! ### Every indecomposable is a lifted module -/

variable (J : D.InjData) (h1 : DegOne D)

/-- `Bᵐᵒᵖ ≅ Alg F₀` from the corner. -/
def eOpB : Bᵐᵒᵖ ≃+* Alg (fun p : D.PV ↦ FB Ls p.1) where
  toFun a := (cornerEquiv Ls S hleft Vx J h1 a.unop).unop
  invFun z := MulOpposite.op ((cornerEquiv Ls S hleft Vx J h1).symm (MulOpposite.op z))
  left_inv a := by simp
  right_inv z := by simp
  map_mul' a b := by simp
  map_add' a b := by simp

theorem eOpB_symm_algebraMap (t : k) :
    (eOpB Ls S hleft Vx J h1).symm (algebraMap k _ t) = algebraMap k Bᵐᵒᵖ t := by
  change MulOpposite.op ((cornerEquiv Ls S hleft Vx J h1).symm
    (MulOpposite.op (algebraMap k _ t))) = _
  rw [← MulOpposite.algebraMap_apply, AlgEquiv.commutes, MulOpposite.algebraMap_apply]

/-- The evaluation of `M_x^B`, as a `B`-linear isomorphism. -/
def evLin : ((ModuleCat.restrictScalars (eOpB Ls S hleft Vx J h1).toRingHom).obj
    (ModuleCat.of (Alg (fun p : D.PV ↦ FB Ls p.1)) (Rep (fun p : D.PV ↦ FB Ls p.1) (FB Ls x)))) ≃ₗ[Bᵐᵒᵖ]
      FB Ls x where
  toFun := evB Ls S hleft Vx x
  invFun := evBInv Ls S hleft Vx x
  left_inv := evBInv_evB Ls S hleft Vx x
  right_inv := evB_evBInv Ls S hleft Vx x
  map_add' := (evB Ls S hleft Vx x).map_add
  map_smul' := fun b f ↦ evB_smul Ls S hleft Vx x b.unop f

/-- **The evaluation of `M_x^B` is `M_x^B`.** -/
def evIso : (ModuleCat.restrictScalars (eOpB Ls S hleft Vx J h1).toRingHom).obj
    (ModuleCat.of (Alg (fun p : D.PV ↦ FB Ls p.1)) (Rep (fun p : D.PV ↦ FB Ls p.1) (FB Ls x))) ≅
      FB Ls x :=
  (evLin Ls S hleft Vx x J h1).toModuleIso

variable (hrad : ∀ (x y : V) (d : ℕ), 1 ≤ d → ∀ f ∈ degreePart c d x y, f ∈ L.rad x y)

include hrad in
/-- The injective labels of the lifted mesh data are those of `A₀`. -/
def injB : (meshB Ls J h1 Vx hrad).InjData where
  S := J.S
  I := J.I
  dimS p q := (finrank_FB Ls J h1 Vx _ _).trans (J.dimS p q)
  dimSI p q := (finrank_FB Ls J h1 Vx _ _).trans (J.dimSI p q)
  dimI p q := (finrank_FB Ls J h1 Vx _ _).trans ((J.dimI p q).trans (finrank_FB Ls J h1 Vx _ _).symm)

include S in
theorem finiteDimensional_B : FiniteDimensional k B := S.φ.finiteDimensional

include hleft hrad Vx J h1 in
/-- **The lifted modules exhaust the indecomposable `B`-modules.** -/
theorem exists_iso_FB (M : RightModuleCat B) (hM : IsFiniteIndecomposable k B M) :
    ∃ x : V, Nonempty (M ≅ FB Ls x) := by
  classical
  have := hM.1
  have := finiteDimensional_B S
  haveI : Module.Finite k Bᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv k)
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (eOpB Ls S hleft Vx J h1)
  let N : ModuleCat (Alg (meshB Ls J h1 Vx hrad).F0) := E.inverse.obj M
  have hfinN : Module.Finite k N := by
    let φ : M →ₗ[k] N :=
      { toFun := fun m ↦ m
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun t m ↦ by
          change algebraMap k Bᵐᵒᵖ t • m = ((eOpB Ls S hleft Vx J h1).symm (algebraMap k _ t)) • m
          rw [eOpB_symm_algebraMap] }
    exact Module.Finite.of_surjective φ fun m ↦ ⟨m, rfl⟩
  haveI hlocM : IsLocalRing (End M) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Bᵐᵒᵖ) M hM.2
  haveI hlocN : IsLocalRing (End N) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
      (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful E.inverse M)
  obtain ⟨x, ⟨e⟩⟩ := (meshB Ls J h1 Vx hrad).exists_iso_evObj (injB Ls Vx J h1 hrad) N
    (MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _)
  exact ⟨x, ⟨(E.counitIso.app M).symm ≪≫ E.functor.mapIso e ≪≫ evIso Ls S hleft Vx x J h1⟩⟩

/-! ### The skeleton of `ind(mod B)` -/

variable {Ls} in
/-- The identity of `M_x^B` from the native `k`-structure. -/
def fbK (x : V) : Rep D.F0 (meshFam Q c x) →ₗ[k] FB Ls x where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' t m := (smul_act Ls x t m).trans rfl

include Vx in
theorem isFiniteIndecomposable_FB (x : V) : IsFiniteIndecomposable k B (FB Ls x) := by
  have hloc : IsLocalRing (End (FB Ls x)) := (localB Ls Vx).end_isLocalRing x
  exact ⟨Module.Finite.of_surjective (fbK x) fun m ↦ ⟨m, rfl⟩,
    @MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _ _ _ _ _ hloc⟩

include Vx in
theorem eq_of_iso_FB {x y : V} (e : FB Ls x ≅ FB Ls y) : x = y := by
  by_contra hxy
  apply (localB Ls Vx).id_not_mem x
  rw [← e.hom_inv_id]
  exact (localB Ls Vx).comp_right ((localB Ls Vx).mem_of_ne hxy e.hom) e.inv

/-- **The lifted modules as a skeleton of `ind(mod B)`.** -/
def skelB : IndSkeleton k B where
  n := Fintype.card V
  obj i := FB Ls ((Fintype.equivFin V).symm i)
  isFiniteIndecomposable i := isFiniteIndecomposable_FB Ls Vx _
  pairwise i j h := (Fintype.equivFin V).symm.injective (eq_of_iso_FB Ls Vx h.some)
  complete M hM := by
    obtain ⟨x, ⟨e⟩⟩ := exists_iso_FB Ls S hleft Vx J h1 hrad M hM
    exact ⟨Fintype.equivFin V x, ⟨e ≪≫ eqToIso (by rw [Equiv.symm_apply_apply])⟩⟩

theorem skelB_obj (x : V) :
    (skelB Ls S hleft Vx J h1 hrad).obj (Fintype.equivFin V x) = FB Ls x := by
  simp [skelB]

include Ls S hleft Vx J h1 hrad in
theorem isRepresentationFinite_B : IsRepresentationFinite k B :=
  ⟨_, (skelB Ls S hleft Vx J h1 hrad).obj, (skelB Ls S hleft Vx J h1 hrad).isFiniteIndecomposable,
    (skelB Ls S hleft Vx J h1 hrad).complete⟩

end MeshWalk

end MultiplicativeBasisDeformations
