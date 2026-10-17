import MultiplicativeBasisDeformations.Foundations.StandardConverse
import MultiplicativeBasisDeformations.Foundations.ARInjData

/-!
# Corollary 2.11: `Γ_{A₀} ≅ Γ_A`

`graded-category.tex` (`cor:same-ar-quiver`): "The Auslander–Reiten quivers of `A₀` and
`A` are isomorphic as translation quivers."

The evaluated modules `M_x` form a skeleton of `ind(mod A₀)` (`skelA0`): they are
indecomposable, pairwise nonisomorphic (`evA_iso_eq`), and every finite-dimensional
indecomposable `A₀`-module is one of them (`evA_complete`, from Proposition 2.10).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] {S : IndSkeleton k A} {b : S.ArrowBases}
  {B : Type w} [Ring B] [Algebra k B] (ψ : B ≃ₐ[k] S.A0 b)

/-- **Distinct vertices have nonisomorphic evaluated modules.** -/
theorem evA_iso_eq {x y : S.ARVertex}
    (h : Nonempty ((evA ψ).obj (S.meshObj b x) ≅ (evA ψ).obj (S.meshObj b y))) : x = y := by
  obtain ⟨u⟩ := h
  obtain ⟨f, hf⟩ := evA_map_surjective ψ x y u.hom
  obtain ⟨g, hg⟩ := evA_map_surjective ψ y x u.inv
  refine MeshWalk.eq_of_comp_eq_id (c := S.arCoefficients b)
    (fun x y ↦ S.finiteDimensional_meshHom b x y) f g (evA_map_injective ψ x x ?_)
  simp only
  rw [Functor.map_comp, hf, hg, Iso.hom_inv_id, CategoryTheory.Functor.map_id]

include ψ in
theorem rep_nontrivial (x : S.ARVertex) :
    ∃ m : CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b x), m ≠ 0 := by
  by_contra h
  push Not at h
  apply evA_id_ne_zero ψ x
  ext m
  change m = 0
  exact h m

variable [FiniteDimensional k B]

/-- **Every indecomposable `B`-module is an evaluated module** (Proposition 2.10). -/
theorem evA_complete (M : RightModuleCat B) (hM : IsFiniteIndecomposable k B M) :
    ∃ x : S.ARVertex, Nonempty (M ≅ (evA ψ).obj (S.meshObj b x)) := by
  classical
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI := hM.1
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (eOp ψ)
  let N := E.inverse.obj M
  have hfinN : FiniteDimensional k N := by
    let φ : M →ₗ[k] N :=
      { toFun := fun m ↦ m
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun t m ↦ by
          change algebraMap k Bᵐᵒᵖ t • m = ((eOp ψ).symm (algebraMap k _ t)) • m
          rw [← eOp_algebraMap ψ t, RingEquiv.symm_apply_apply] }
    exact Module.Finite.of_surjective φ fun m ↦ ⟨m, rfl⟩
  obtain ⟨μ, _, _, W, ⟨L⟩⟩ := (S.arInjData b).essSurj (X := N)
  haveI : Module.Finite k Bᵐᵒᵖ := inferInstance
  haveI hlocM : IsLocalRing (End M) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Bᵐᵒᵖ) M hM.2
  haveI hlocN : IsLocalRing (End N) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
      (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful E.inverse M)
  -- the family has one member
  have hsub : ∀ j₁ j₂ : μ, j₁ = j₂ := by
    intro j₁ j₂
    by_contra hne
    let π : (S.arMeshData b).EZ W →ₗ[CatAlg.Alg (S.arMeshData b).F0] (S.arMeshData b).EZ W :=
      LinearMap.pi fun j ↦ if j = j₁ then LinearMap.proj j else 0
    have hπ : ∀ v j, π v j = if j = j₁ then v j else 0 := by
      intro v j; simp only [π, LinearMap.pi_apply]; split_ifs <;> rfl
    let e : End N := ModuleCat.ofHom (X := N) (Y := N) (L.symm.toLinearMap ∘ₗ π ∘ₗ L.toLinearMap)
    have he : ∀ n, e.hom n = L.symm (π (L n)) := fun _ ↦ rfl
    have hidem : e * e = e := by
      refine ModuleCat.hom_ext (LinearMap.ext fun n ↦ ?_)
      rw [End.mul_def, ModuleCat.hom_comp, LinearMap.comp_apply, he, he,
        LinearEquiv.apply_symm_apply]
      congr 1
      funext j
      rw [hπ, hπ]
      split_ifs <;> rfl
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := e) (b := 1 - e) (add_sub_cancel e 1)
      with h | h
    · -- `e = 1`, so `π` is the identity, contradiction at `j₂`
      have h1 : e = 1 := h.mul_left_cancel (by rw [hidem, mul_one])
      obtain ⟨m, hm⟩ := rep_nontrivial ψ (W j₂)
      apply hm
      have := congrArg (fun φ : End N ↦ L (φ.hom (L.symm (Pi.single j₂ m)))) h1
      simp only [he, LinearEquiv.apply_symm_apply] at this
      have h2 := congrFun this j₂
      rw [hπ, if_neg (Ne.symm hne)] at h2
      change 0 = (L (L.symm (Pi.single j₂ m))) j₂ at h2
      rw [LinearEquiv.apply_symm_apply, Pi.single_eq_same] at h2
      exact h2.symm
    · -- `e = 0`, so `π` is zero, contradiction at `j₁`
      have hidem' : (1 - e) * (1 - e) = 1 - e := by
        rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, hidem]; abel
      have h1 : 1 - e = 1 := h.mul_left_cancel (by rw [hidem', mul_one])
      have h0 : e = 0 := by
        have := congrArg (1 - ·) h1
        simpa using this
      obtain ⟨m, hm⟩ := rep_nontrivial ψ (W j₁)
      apply hm
      have := congrArg (fun φ : End N ↦ L (φ.hom (L.symm (Pi.single j₁ m)))) h0
      simp only [he, LinearEquiv.apply_symm_apply] at this
      have h2 := congrFun this j₁
      rw [hπ, if_pos rfl, Pi.single_eq_same] at h2
      rw [h2]
      simp
  -- the family is nonempty
  have hne : Nonempty μ := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hM.2.1
    haveI : Subsingleton ((S.arMeshData b).EZ W) := ⟨fun v w ↦ funext fun j ↦ isEmptyElim j⟩
    haveI : Subsingleton N := ⟨fun n n' ↦ L.injective (Subsingleton.elim _ _)⟩
    haveI : Subsingleton M := ‹Subsingleton N›
    exact ModuleCat.isZero_of_subsingleton _
  obtain ⟨j₀⟩ := hne
  haveI : Subsingleton μ := ⟨hsub⟩
  haveI : Unique μ := uniqueOfSubsingleton j₀
  have L' := L.trans (LinearEquiv.piUnique (CatAlg.Alg (S.arMeshData b).F0) _)
  refine ⟨W default, ⟨(E.counitIso.app M).symm ≪≫ E.functor.mapIso L'.toModuleIso⟩⟩

/-! ### The skeleton of `ind(mod A₀)` -/

section A0

variable (S b)

theorem finiteDimensional_A0 : FiniteDimensional k (S.A0 b) := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : FiniteDimensional k (CatAlg.Alg (S.arMeshData b).F0) := CatAlg.finiteDimensional_alg
  exact Module.Finite.equiv (MulOpposite.opLinearEquiv k)

instance instFiniteDimensionalA0 : FiniteDimensional k (S.A0 b) := finiteDimensional_A0 S b

/-- The identity of `A₀`. -/
abbrev ψ₀ : S.A0 b ≃ₐ[k] S.A0 b := AlgEquiv.refl

/-- **The evaluated modules as a skeleton of `ind(mod A₀)`.** -/
abbrev skelA0 : IndSkeleton k (S.A0 b) where
  n := S.n
  obj := fun x ↦ (evA (ψ₀ S b)).obj (S.meshObj b x)
  isFiniteIndecomposable := fun x ↦ evA_isFiniteIndecomposable (ψ₀ S b) x
  pairwise := fun _ _ h ↦ evA_iso_eq (ψ₀ S b) h
  complete := fun M hM ↦ evA_complete (ψ₀ S b) M hM

/-- The identification of the skeleton with the evaluation. -/
abbrev θ₀ (x : S.ARVertex) :
    (evA (ψ₀ S b)).obj (S.meshObj b x) ≅ (skelA0 S b).obj ((id : S.ARVertex → Fin S.n) x) :=
  Iso.refl _

variable [Finite S.ARVertex]

/-- `Φ` as a linear map. -/
def ΦL (x y : Fin S.n) :
    (S.meshObj b (S.vertex x) ⟶ S.meshObj b (S.vertex y)) →ₗ[k]
      ((skelA0 S b).ind x ⟶ (skelA0 S b).ind y) where
  toFun := Φm (ψ₀ S b) (skelA0 S b) id (θ₀ S b)
  map_add' := Φm_add (ψ₀ S b) (skelA0 S b) id (θ₀ S b)
  map_smul' := Φm_smul (ψ₀ S b) (skelA0 S b) id (θ₀ S b)

theorem ΦL_mem_iff (m : ℕ) (x y : Fin S.n) (g : S.meshObj b (S.vertex x) ⟶ S.meshObj b (S.vertex y)) :
    ΦL S b x y g ∈ (skelA0 S b).radPow m _ _ ↔ MeshWalk.Ge (S.arCoefficients b) m g :=
  mem_radPow_Φm_iff (ψ₀ S b) (skelA0 S b) (θ₀ S b) Function.bijective_id m g

theorem ΦL_surjective (x y : Fin S.n) : Function.Surjective (ΦL S b x y) :=
  fun f ↦ Φm_surjective (ψ₀ S b) (skelA0 S b) id (θ₀ S b) f

/-- Degree-one morphisms into the radical. -/
def deg1Rad (x y : Fin S.n) :
    ScalarMeshCategory.degreePart (S.arCoefficients b) 1 (S.vertex x) (S.vertex y) →ₗ[k]
      (skelA0 S b).radPow 1 ((skelA0 S b).ind x) ((skelA0 S b).ind y) :=
  LinearMap.codRestrict _ ((ΦL S b x y).comp (Submodule.subtype _)) fun g ↦
    (ΦL_mem_iff S b 1 x y g).2 (MeshWalk.ge_of_mem g.2 le_rfl)

theorem deg1Rad_coe (x y : Fin S.n)
    (g : ScalarMeshCategory.degreePart (S.arCoefficients b) 1 (S.vertex x) (S.vertex y)) :
    (deg1Rad S b x y g : (skelA0 S b).ind x ⟶ (skelA0 S b).ind y) = ΦL S b x y g := rfl

/-- The irreducible maps of `A₀` are the degree-one morphisms of `C`. -/
def irrMapA0 (x y : Fin S.n) :
    ScalarMeshCategory.degreePart (S.arCoefficients b) 1 (S.vertex x) (S.vertex y) →ₗ[k]
      (skelA0 S b).Irr ((skelA0 S b).ind x) ((skelA0 S b).ind y) :=
  (Submodule.mkQ _).comp (deg1Rad S b x y)

theorem irrMapA0_injective (x y : Fin S.n) : Function.Injective (irrMapA0 S b x y) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro g hg
  rw [LinearMap.mem_ker, irrMapA0, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    deg1Rad_coe] at hg
  have h1 := (ΦL_mem_iff S b 2 x y g).1 hg 1 (by omega)
  rw [ScalarMeshCategory.degProj_of_mem _ g.2, if_pos rfl] at h1
  rw [Submodule.mem_bot]
  exact Subtype.ext h1

theorem irrMapA0_surjective (x y : Fin S.n) : Function.Surjective (irrMapA0 S b x y) := by
  intro c
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨g, rfl⟩ := ΦL_surjective S b x y f
  have hg := (ΦL_mem_iff S b 1 x y g).1 hf
  have key : ΦL S b x y (ScalarMeshCategory.degProj (S.arCoefficients b) 1 _ _ g) -
      ΦL S b x y g ∈ (skelA0 S b).radPow 2 ((skelA0 S b).ind x) ((skelA0 S b).ind y) := by
    rw [← map_sub, ΦL_mem_iff]
    intro d hd
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · rw [map_sub, ScalarMeshCategory.degProj_of_mem _ (ScalarMeshCategory.degProj_mem _ 1 g),
        if_neg (by omega), hg 0 (by omega), sub_zero]
    · rw [map_sub, ScalarMeshCategory.degProj_of_mem _ (ScalarMeshCategory.degProj_mem _ 1 g),
        if_pos rfl, sub_self]
  refine ⟨⟨_, ScalarMeshCategory.degProj_mem _ 1 g⟩, ?_⟩
  exact (Submodule.Quotient.eq _).2 key

/-- **`Γ_{A₀}` and `Γ_A` have the same arrows.** -/
theorem finrank_irr_A0 (x y : Fin S.n) :
    Module.finrank k ((skelA0 S b).Irr ((skelA0 S b).ind x) ((skelA0 S b).ind y)) =
      Module.finrank k (S.Irr (S.ind x) (S.ind y)) := by
  obtain ⟨-, φ, -, -⟩ := S.gradedRealization_full b
  rw [← (LinearEquiv.ofBijective _ ⟨irrMapA0_injective S b x y,
    irrMapA0_surjective S b x y⟩).finrank_eq]
  exact (φ 1 x y).finrank_eq

end A0

end MultiplicativeBasisDeformations.IndSkeleton
