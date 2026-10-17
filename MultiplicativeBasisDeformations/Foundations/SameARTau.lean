import MultiplicativeBasisDeformations.Foundations.SameARQuiver

/-!
# Corollary 2.11: the translations of `Γ_{A₀}` and `Γ_A` agree

`graded-category.tex` (proof of `cor:same-ar-quiver`): "every right mesh map is right
almost split. ... Thus the meshes are the almost split sequences and give the translation."

Evaluated at the projective labels, the right mesh map at `x` is
`f_x : ⊕_a M_{mid a} → M_x` (`mesh0`), with kernel `M_{τ x}` at a nonprojective `x`
(`tau0`) and injective at a projective `x`.

Deviation: instead of proving that `f_x` is right minimal by
degrees, we compare `f_x` with the chosen minimal right almost split map `c` of the vendored
library. Every component of `c` is radical, so `c` factors through `f_x` (`c = h' f_x`), and
`f_x` is not split epi, so `f_x = h c`. Minimality of `c` makes `h' h` invertible, which
identifies `ker c` with a summand of `ker f_x`; as `ker f_x ≅ M_{τ x}` is indecomposable, the
two kernels agree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg.MeshData

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}
  {L : LocalFamily (k := k) F} (D : MeshData F L)

/-- The evaluated middle term `⊕_a M_{mid a}`. -/
abbrev P0 (x : ι) := ∀ a : D.Mid x, Rep D.F0 (F (D.mid x a))

/-- The evaluated right mesh map `⊕_a M_{mid a} → M_x`. -/
def mesh0 (x : ι) : D.P0 x →ₗ[Alg D.F0] Rep D.F0 (F x) :=
  ∑ a, (repMap (D.p x a)).comp (LinearMap.proj a)

theorem mesh0_apply (x : ι) (m : D.P0 x) (w : D.PV) :
    D.mesh0 x m w = ∑ a, m a w ≫ D.p x a := by
  rw [mesh0, LinearMap.sum_apply, Rep.sum_apply]
  rfl

/-- The evaluated left mesh map `M_{τ x} → ⊕_a M_{mid a}`. -/
def tau0 (x : ι) (hx : ¬ D.proj x) : Rep D.F0 (F (D.tau x hx)) →ₗ[Alg D.F0] D.P0 x :=
  LinearMap.pi fun a ↦ repMap (D.q x hx a)

theorem tau0_apply (x : ι) (hx : ¬ D.proj x) (z : Rep D.F0 (F (D.tau x hx))) (a : D.Mid x)
    (w : D.PV) : D.tau0 x hx z a w = z w ≫ D.q x hx a := rfl

theorem mesh0_tau0 (x : ι) (hx : ¬ D.proj x) (z : Rep D.F0 (F (D.tau x hx))) :
    D.mesh0 x (D.tau0 x hx z) = 0 := by
  ext w
  rw [mesh0_apply]
  simp only [tau0_apply, Category.assoc]
  rw [← Preadditive.comp_sum, D.comp_zero, Limits.comp_zero]
  rfl

theorem tau0_injective (x : ι) (hx : ¬ D.proj x) : Function.Injective (D.tau0 x hx) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro r hr
  rw [LinearMap.mem_ker] at hr
  rw [Submodule.mem_bot]
  ext w
  exact D.cov_mono x hx w.1 (r w) fun a ↦ congrFun (congrFun hr a) w

theorem exists_tau0 (x : ι) (hx : ¬ D.proj x) (m : D.P0 x) (hm : D.mesh0 x m = 0) :
    ∃ z, D.tau0 x hx z = m := by
  choose z hz using fun w : D.PV ↦ D.cov_exact x hx w.1 (fun a ↦ m a w) (by
    have := congrFun hm w
    rwa [mesh0_apply] at this)
  refine ⟨(z : Rep D.F0 (F (D.tau x hx))), ?_⟩
  ext a w
  exact (hz w a).symm

theorem mesh0_injective (x : ι) (hx : D.proj x) : Function.Injective (D.mesh0 x) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  rw [Submodule.mem_bot]
  ext a w
  exact D.proj_mono x hx w.1 (fun a ↦ m a w) (by
    have := congrFun hm w
    rwa [mesh0_apply] at this) a

theorem mesh0_surjective (x : ι) (hx : ¬ D.proj x) : Function.Surjective (D.mesh0 x) := by
  intro r
  have hne : ∀ w : D.PV, w.1 ≠ x := fun w h ↦ hx (h ▸ w.2)
  choose g hg using fun w : D.PV ↦ D.image x w.1 (r w) (L.mem_of_ne (hne w) _)
  refine ⟨fun a w ↦ g w a, ?_⟩
  ext w
  exact (D.mesh0_apply x _ w).trans (hg w).symm

/-- A radical map factors through the evaluated mesh map. -/
theorem exists_repMap_eq_mesh0 (x y : ι) (g : F y ⟶ F x) (hg : g ∈ L.rad y x) :
    ∃ h : ∀ a : D.Mid x, F y ⟶ F (D.mid x a),
      repMap (F := D.F0) g = (D.mesh0 x).comp (LinearMap.pi fun a ↦ repMap (h a)) := by
  obtain ⟨h, rfl⟩ := D.image x y g hg
  refine ⟨h, ?_⟩
  ext m w
  rw [LinearMap.comp_apply, mesh0_apply, repMap_apply, Preadditive.comp_sum]
  simp only [LinearMap.pi_apply, repMap_apply, Category.assoc]

/-- A composite through the mesh arrows is radical. -/
theorem sum_comp_p_mem_rad (x y : ι) (g : ∀ a : D.Mid x, F y ⟶ F (D.mid x a)) :
    ∑ a, g a ≫ D.p x a ∈ L.rad y x :=
  Submodule.sum_mem _ fun a _ ↦ L.comp_left _ (D.p_rad x a)

end CatAlg.MeshData

/-- A map out of a biproduct factors through `f` when each component does. -/
theorem exists_factor_of_biproduct {C : Type*} [Category C] [Preadditive C] {J : Type*}
    {X : J → C} {hX : Limits.HasBiproduct X} {E Z P : C} (d : E ≅ ⨁ X) (c : E ⟶ Z)
    (f : P ⟶ Z) (hc : ∀ j, ∃ l : X j ⟶ P, l ≫ f = Limits.biproduct.ι X j ≫ d.inv ≫ c) :
    ∃ h : E ⟶ P, h ≫ f = c := by
  choose l hl using hc
  refine ⟨d.hom ≫ Limits.biproduct.desc l, ?_⟩
  have : Limits.biproduct.desc l ≫ f = d.inv ≫ c := by
    refine Limits.biproduct.hom_ext' _ _ fun j ↦ ?_
    rw [Limits.biproduct.ι_desc_assoc, hl]
  rw [Category.assoc, this, Iso.hom_inv_id_assoc]

theorem not_isSplitEpi_comp {C : Type*} [Category C] {X Y Z : C} (g : X ⟶ Y) (c : Y ⟶ Z)
    (hc : ¬ IsSplitEpi c) : ¬ IsSplitEpi (g ≫ c) := by
  rintro ⟨⟨s⟩⟩
  exact hc (IsSplitEpi.mk' ⟨s.section_ ≫ g, by simpa only [Category.assoc] using s.id⟩)

namespace IndSkeleton

open scoped ModuleCat.Algebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

instance instNoetherianA0 : IsNoetherianRing (S.A0 b)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- Restriction along `A₀ᵒᵖ ≅ Λ`. -/
abbrev resA0 := ModuleCat.restrictScalars.{w} (eOp (ψ₀ S b)).toRingHom

/-- The evaluated middle term, as an `A₀`-module. -/
abbrev PM (x : S.ARVertex) : RightModuleCat (S.A0 b) :=
  (resA0 S b).obj (ModuleCat.of _ ((S.arMeshData b).P0 x))

theorem finite_PM (x : S.ARVertex) : Module.Finite k (PM S b x) := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : FiniteDimensional k ((S.arMeshData b).P0 x) := by
    unfold CatAlg.MeshData.P0
    infer_instance
  let φ : (S.arMeshData b).P0 x →ₗ[k] PM S b x :=
    { toFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun t m ↦ by
        change _ = (eOp (ψ₀ S b) (algebraMap k (S.A0 b)ᵐᵒᵖ t)) • m
        rw [eOp_algebraMap, algebraMap_smul] }
  exact Module.Finite.of_surjective φ fun m ↦ ⟨m, rfl⟩

/-- The evaluated middle term in `mod A₀`. -/
abbrev PFG (x : S.ARVertex) : ModCat (S.A0 b) :=
  @MBDVendor.Magnitude.RightModule.finitelyGeneratedOfFiniteDimensional k _ (S.A0 b) _ _
    (PM S b x) (finite_PM S b x)

/-- The evaluated right mesh map `f_x` in `mod A₀`. -/
def fFG (x : S.ARVertex) : PFG S b x ⟶ (skelA0 S b).fg x :=
  ObjectProperty.homMk ((resA0 S b).map (ModuleCat.ofHom ((S.arMeshData b).mesh0 x)))

theorem fFG_apply (x : S.ARVertex) (m : (S.arMeshData b).P0 x) :
    (fFG S b x).hom.hom m = (S.arMeshData b).mesh0 x m := rfl

/-- The evaluated left mesh map in `mod A₀`. -/
def tFG (x : S.ARVertex) (hx : ¬ (S.arMeshData b).proj x) :
    (skelA0 S b).fg ((S.arMeshData b).tau x hx) ⟶ PFG S b x :=
  ObjectProperty.homMk ((resA0 S b).map (ModuleCat.ofHom ((S.arMeshData b).tau0 x hx)))

theorem tFG_apply (x : S.ARVertex) (hx : ¬ (S.arMeshData b).proj x)
    (z : CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b ((S.arMeshData b).tau x hx))) :
    (tFG S b x hx).hom.hom z = (S.arMeshData b).tau0 x hx z := rfl

theorem tFG_fFG (x : S.ARVertex) (hx : ¬ (S.arMeshData b).proj x) :
    tFG S b x hx ≫ fFG S b x = 0 := by
  ext z
  exact (S.arMeshData b).mesh0_tau0 x hx z

/-- `tFG` is a kernel of `fFG`. -/
theorem exists_lift_tFG (x : S.ARVertex) (hx : ¬ (S.arMeshData b).proj x) {Z : ModCat (S.A0 b)}
    (g : Z ⟶ PFG S b x) (hg : g ≫ fFG S b x = 0) : ∃ s, s ≫ tFG S b x hx = g := by
  let τl : ((skelA0 S b).fg ((S.arMeshData b).tau x hx)).obj →ₗ[(S.A0 b)ᵐᵒᵖ] (PFG S b x).obj :=
    (tFG S b x hx).hom.hom
  have hinj : Function.Injective τl := (S.arMeshData b).tau0_injective x hx
  have hmem : ∀ z, g.hom.hom z ∈ LinearMap.range τl := fun z ↦ by
    have h0 : (S.arMeshData b).mesh0 x (g.hom.hom z) = 0 := by
      have := congrArg (fun φ : Z ⟶ (skelA0 S b).fg x ↦ φ.hom.hom z) hg
      exact this
    obtain ⟨y, hy⟩ := (S.arMeshData b).exists_tau0 x hx _ h0
    exact ⟨y, hy⟩
  let e := LinearEquiv.ofInjective τl hinj
  refine ⟨ObjectProperty.homMk (ModuleCat.ofHom (X := Z.obj)
    (Y := ((skelA0 S b).fg ((S.arMeshData b).tau x hx)).obj)
    (e.symm.toLinearMap ∘ₗ g.hom.hom.codRestrict _ hmem)), ?_⟩
  ext z
  exact congrArg Subtype.val (e.apply_symm_apply ⟨g.hom.hom z, hmem z⟩)

/-- `f_x` is not split epi: its components are radical. -/
theorem fFG_not_isSplitEpi (x : S.ARVertex) : ¬ IsSplitEpi (fFG S b x) := by
  rintro ⟨⟨s⟩⟩
  have hcomp : ∀ a : (S.arMeshData b).Mid x,
      ∃ g : S.meshObj b x ⟶ S.meshObj b ((S.arMeshData b).mid x a),
        ∀ m, (s.section_.hom.hom m) a = CatAlg.repMap g m := by
    intro a
    let sa : (evA (ψ₀ S b)).obj (S.meshObj b x) ⟶
        (evA (ψ₀ S b)).obj (S.meshObj b ((S.arMeshData b).mid x a)) :=
      s.section_.hom ≫ (resA0 S b).map (ModuleCat.ofHom (LinearMap.proj a))
    obtain ⟨g, hg⟩ := evA_map_surjective (ψ₀ S b) x _ sa
    exact ⟨g, fun m ↦ (congrArg (fun φ ↦ φ.hom m) hg).symm⟩
  choose g hg using hcomp
  apply (S.arLocal b).id_not_mem x
  have key : ∑ a, g a ≫ (S.arMeshData b).p x a = 𝟙 _ := by
    apply evA_map_injective (ψ₀ S b) x x
    simp only
    rw [CategoryTheory.Functor.map_id]
    refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    change CatAlg.repMap _ m = m
    have hid : (S.arMeshData b).mesh0 x (s.section_.hom.hom m) = m :=
      congrArg (fun φ ↦ φ.hom.hom m) s.id
    conv_rhs => rw [← hid]
    ext w
    rw [CatAlg.MeshData.mesh0_apply, CatAlg.repMap_apply, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hg a m, CatAlg.repMap_apply, Category.assoc]
  rw [← key]
  exact (S.arMeshData b).sum_comp_p_mem_rad x x g

/-- A map into `M_x` that is not split epi factors through `f_x`. -/
theorem exists_factor_fFG (x y : S.ARVertex) (g : (skelA0 S b).fg y ⟶ (skelA0 S b).fg x)
    (hg : ¬ IsSplitEpi g) : ∃ l : (skelA0 S b).fg y ⟶ PFG S b x, l ≫ fFG S b x = g := by
  obtain ⟨g', hg'⟩ := evA_map_surjective (ψ₀ S b) y x g.hom
  by_cases hr : g' ∈ (S.arLocal b).rad y x
  · obtain ⟨h, hh⟩ := (S.arMeshData b).exists_repMap_eq_mesh0 x y g' hr
    refine ⟨ObjectProperty.homMk ((resA0 S b).map
      (ModuleCat.ofHom (LinearMap.pi fun a ↦ CatAlg.repMap (h a)))), ?_⟩
    ext m
    change (S.arMeshData b).mesh0 x _ = g.hom.hom m
    rw [← hg']
    change _ = CatAlg.repMap g' m
    rw [hh]
    rfl
  · exfalso
    have hxy : y = x := by
      by_contra hne
      exact hr ((S.arLocal b).mem_of_ne hne _)
    subst hxy
    have hu := (S.arLocal b).isUnit_of_not_mem (f := g') hr
    have : IsIso g' := (isUnit_iff_isIso _).1 hu
    apply hg
    have hid : (ObjectProperty.homMk (inv ((evA (ψ₀ S b)).map g')) :
        (skelA0 S b).fg y ⟶ (skelA0 S b).fg y) ≫ g = 𝟙 _ := by
      ext1
      change ModuleCat.Hom.hom (inv ((evA (ψ₀ S b)).map g') ≫ g.hom) =
        ModuleCat.Hom.hom (𝟙 ((evA (ψ₀ S b)).obj (S.meshObj b y)))
      rw [← hg', IsIso.inv_hom_id]
    exact IsSplitEpi.mk' ⟨_, hid⟩

/-! ### Comparison with the chosen minimal right almost split map -/

/-- The chosen minimal right almost split map of `A₀` ending at `M_x`. -/
abbrev mras (x : S.ARVertex) := (skelA0 S b).toVendor.minimalRightAlmostSplitAt x

/-- `c = h' f_x`, `f_x = h c`, and `h' h` is invertible. -/
theorem exists_comparison (x : S.ARVertex) :
    ∃ (h' : (mras S b x).middle ⟶ PFG S b x) (h : PFG S b x ⟶ (mras S b x).middle),
      h' ≫ fFG S b x = (mras S b x).map ∧ h ≫ (mras S b x).map = fFG S b x ∧
        IsIso (h' ≫ h) := by
  obtain ⟨h', hh'⟩ := exists_factor_of_biproduct (mras S b x).decomposition (mras S b x).map
    (fFG S b x) fun j ↦ exists_factor_fFG S b x ((mras S b x).label j) _
      (not_isSplitEpi_comp _ _
        (not_isSplitEpi_comp _ _ (mras S b x).rightAlmostSplit.not_isSplitEpi))
  obtain ⟨h, hh⟩ := (mras S b x).rightAlmostSplit.factors (fFG S b x) (fFG_not_isSplitEpi S b x)
  refine ⟨h', h, hh', hh, (mras S b x).rightMinimal _ ?_⟩
  rw [Category.assoc, hh, hh']

theorem subsingleton_of_id_eq_zero {M : ModCat (S.A0 b)} (h : 𝟙 M = 0) : Subsingleton M := by
  let U := forget₂ (ModCat (S.A0 b)) (RightModuleCat (S.A0 b))
  have : Limits.IsZero (U.obj M) := U.map_isZero ((Limits.IsZero.iff_id_eq_zero _).2 h)
  exact ModuleCat.isZero_iff_subsingleton.mp this

/-- At a projective vertex of `Γ_A`, `M_x` is projective. -/
theorem projective_fg_of_proj (x : S.ARVertex) (hx : (S.arMeshData b).proj x) :
    Projective ((skelA0 S b).fg x) := by
  by_contra hP
  obtain ⟨h', h, hh', hh, hiso⟩ := exists_comparison S b x
  have hnt := ((skelA0 S b).toVendor.chosenRight_kernel_ar_sequence ⟨x, hP⟩).2.2.1.nontrivial
  have h1 : Limits.kernel.ι (mras S b x).map ≫ h' = 0 := by
    have h0 : Limits.kernel.ι (mras S b x).map ≫ h' ≫ fFG S b x = 0 := by
      rw [hh', Limits.kernel.condition]
    ext m
    apply (S.arMeshData b).mesh0_injective x hx
    refine (congrArg (fun φ ↦ φ.hom.hom m) h0).trans ?_
    exact (map_zero ((S.arMeshData b).mesh0 x)).symm
  have h2 : Limits.kernel.ι (mras S b x).map = 0 := by
    have : Limits.kernel.ι (mras S b x).map ≫ (h' ≫ h) ≫ inv (h' ≫ h) =
        Limits.kernel.ι (mras S b x).map := by simp
    rw [← this, ← Category.assoc, ← Category.assoc, h1, Limits.zero_comp, Limits.zero_comp]
  have h3 : 𝟙 (Limits.kernel (mras S b x).map) = 0 :=
    (cancel_mono (Limits.kernel.ι (mras S b x).map)).1 (by rw [h2]; simp)
  exact (not_subsingleton_iff_nontrivial.mpr hnt) (subsingleton_of_id_eq_zero S b h3)

/-- At a nonprojective vertex of `Γ_A`, `M_x` is not projective. -/
theorem not_projective_of_not_proj (x : S.ARVertex) (hx : ¬ (S.arMeshData b).proj x) :
    ¬ Projective ((skelA0 S b).fg x) := by
  intro hP
  have : Epi (fFG S b x) := by
    refine ⟨fun {Z} u v huv ↦ ?_⟩
    ext n
    obtain ⟨m, rfl⟩ := (S.arMeshData b).mesh0_surjective x hx n
    exact congrArg (fun φ ↦ φ.hom.hom m) huv
  exact fFG_not_isSplitEpi S b x
    (IsSplitEpi.mk' ⟨Projective.factorThru (𝟙 _) (fFG S b x), Projective.factorThru_comp _ _⟩)

/-- **The translations agree.** -/
theorem rightTranslationLabel_eq (x : S.ARVertex) (hx : ¬ (S.arMeshData b).proj x)
    (hP : ¬ Projective ((skelA0 S b).toVendor.fgObj x)) :
    (skelA0 S b).toVendor.rightTranslationLabel ⟨x, hP⟩ = (S.arMeshData b).tau x hx := by
  obtain ⟨h', h, hh', hh, hiso⟩ := exists_comparison S b x
  have huc : inv (h' ≫ h) ≫ (mras S b x).map = (mras S b x).map := by
    rw [IsIso.inv_comp_eq, Category.assoc, hh, hh']
  let t := tFG S b x hx ≫ h ≫ inv (h' ≫ h)
  have ht : t ≫ (mras S b x).map = 0 := by
    simp only [t, Category.assoc, huc, hh, tFG_fFG]
  let t' := Limits.kernel.lift (mras S b x).map t ht
  have hs0 : (Limits.kernel.ι (mras S b x).map ≫ h') ≫ fFG S b x = 0 := by
    rw [Category.assoc, hh', Limits.kernel.condition]
  obtain ⟨s', hs'⟩ := exists_lift_tFG S b x hx _ hs0
  have hst : s' ≫ t' = 𝟙 _ := by
    refine (cancel_mono (Limits.kernel.ι (mras S b x).map)).1 ?_
    rw [Category.assoc, Limits.kernel.lift_ι, Category.id_comp]
    simp only [t]
    rw [← Category.assoc, hs', Category.assoc, ← Category.assoc h' h, IsIso.hom_inv_id,
      Category.comp_id]
  let e := t' ≫ s'
  have he : e ≫ e = e := by
    simp only [e, Category.assoc]
    rw [← Category.assoc s' t', hst, Category.id_comp]
  have hne : e ≠ 0 := by
    intro h0
    have hnt := ((skelA0 S b).toVendor.chosenRight_kernel_ar_sequence ⟨x, hP⟩).2.2.1.nontrivial
    have h3 : 𝟙 (Limits.kernel (mras S b x).map) = 0 := by
      calc 𝟙 (Limits.kernel (mras S b x).map) = (s' ≫ t') ≫ (s' ≫ t') := by
            rw [hst, Category.id_comp]
        _ = s' ≫ e ≫ t' := by simp only [e, Category.assoc]
        _ = 0 := by rw [h0, Limits.zero_comp, Limits.comp_zero]
    exact (not_subsingleton_iff_nontrivial.mpr hnt) (subsingleton_of_id_eq_zero S b h3)
  have he1 : e = 𝟙 _ := by
    let E : End ((evA (ψ₀ S b)).obj (S.meshObj b ((S.arMeshData b).tau x hx))) := e.hom
    have hE : E * E = E := by
      rw [End.mul_def]
      exact congrArg (fun φ ↦ φ.hom) he
    have hE0 : E ≠ 0 := fun h0 ↦ hne (by ext1; exact congrArg ModuleCat.Hom.hom h0)
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := E) (b := 1 - E) (add_sub_cancel E 1)
      with hu | hu
    · have h1 : E = 1 := hu.mul_left_cancel (by rw [hE, mul_one])
      ext1
      exact congrArg ModuleCat.Hom.hom h1
    · exfalso
      have hE' : (1 - E) * (1 - E) = 1 - E := by
        rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, hE]; abel
      have h1 : 1 - E = 1 := hu.mul_left_cancel (by rw [hE', mul_one])
      exact hE0 (sub_eq_self.mp h1)
  have iso : Limits.kernel (mras S b x).map ≅ (skelA0 S b).fg ((S.arMeshData b).tau x hx) :=
    ⟨s', t', hst, he1⟩
  exact (skelA0 S b).toVendor.fgObj_skeletal
    ⟨((skelA0 S b).toVendor.rightTranslationKernelIso ⟨x, hP⟩).symm ≪≫ iso⟩

/-! ### Corollary 2.11 -/

theorem nonprojective_A0_iff (x : Fin S.n) :
    (skelA0 S b).vertex x ∈ (skelA0 S b).nonprojectiveVertices ↔
      S.vertex x ∈ S.nonprojectiveVertices := by
  constructor
  · intro hP
    by_contra hx
    exact hP (projective_fg_of_proj S b x hx)
  · intro hx hP
    exact not_projective_of_not_proj S b x (not_not.2 hx) hP

theorem arTau_A0 (x : Fin S.n) (h1 : (skelA0 S b).vertex x ∈ (skelA0 S b).nonprojectiveVertices)
    (h2 : S.vertex x ∈ S.nonprojectiveVertices) :
    ((skelA0 S b).arTau ⟨_, h1⟩).1 = (S.arTau ⟨_, h2⟩).1 :=
  rightTranslationLabel_eq S b x (not_not.2 h2) h1

theorem noninjective_A0_iff (x : Fin S.n) :
    (skelA0 S b).vertex x ∈ (skelA0 S b).noninjectiveVertices ↔
      S.vertex x ∈ S.noninjectiveVertices := by
  constructor
  · intro hx
    let z := (skelA0 S b).arTau.symm ⟨_, hx⟩
    have hz : S.vertex z.1 ∈ S.nonprojectiveVertices := (nonprojective_A0_iff S b z.1).1 z.2
    have e1 := arTau_A0 S b z.1 z.2 hz
    have e2 : ((skelA0 S b).arTau z).1 = x := by
      simp only [z, Equiv.apply_symm_apply]
      rfl
    change ((skelA0 S b).arTau z).1 = _ at e1
    rw [e2] at e1
    rw [e1]
    exact (S.arTau ⟨_, hz⟩).2
  · intro hx
    let z := S.arTau.symm ⟨_, hx⟩
    have hz : (skelA0 S b).vertex z.1 ∈ (skelA0 S b).nonprojectiveVertices :=
      (nonprojective_A0_iff S b z.1).2 z.2
    have e1 := arTau_A0 S b z.1 hz z.2
    have e2 : (S.arTau z).1 = x := by
      simp only [z, Equiv.apply_symm_apply]
      rfl
    change (S.arTau ⟨S.vertex z.1, z.2⟩).1 = x at e2
    rw [e2] at e1
    change x ∈ (skelA0 S b).noninjectiveVertices
    rw [← e1]
    exact ((skelA0 S b).arTau ⟨_, hz⟩).2

/-- **Corollary 2.11** (`cor:same-ar-quiver`): `Γ_{A₀} ≅ Γ_A` as translation quivers. Both
have the vertex set `Fin n`, and the identity matches the arrows, the nonprojective and
noninjective vertices, and the translations. -/
theorem sameARQuiver :
    (∀ x y : Fin S.n, Nonempty
      (((skelA0 S b).vertex x ⟶ (skelA0 S b).vertex y) ≃ (S.vertex x ⟶ S.vertex y))) ∧
    (∀ x : Fin S.n, (skelA0 S b).vertex x ∈ (skelA0 S b).nonprojectiveVertices ↔
      S.vertex x ∈ S.nonprojectiveVertices) ∧
    (∀ x : Fin S.n, (skelA0 S b).vertex x ∈ (skelA0 S b).noninjectiveVertices ↔
      S.vertex x ∈ S.noninjectiveVertices) ∧
    ∀ (x : Fin S.n) (h1 : (skelA0 S b).vertex x ∈ (skelA0 S b).nonprojectiveVertices)
      (h2 : S.vertex x ∈ S.nonprojectiveVertices),
        ((skelA0 S b).arTau ⟨_, h1⟩).1 = (S.arTau ⟨_, h2⟩).1 :=
  ⟨fun x y ↦ ⟨finCongr (finrank_irr_A0 S b x y)⟩, nonprojective_A0_iff S b,
    noninjective_A0_iff S b, arTau_A0 S b⟩

end IndSkeleton

end MultiplicativeBasisDeformations
