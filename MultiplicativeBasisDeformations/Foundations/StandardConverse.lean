import MultiplicativeBasisDeformations.Foundations.MeshRadical
import MultiplicativeBasisDeformations.Foundations.FilteredNormalForm
import MultiplicativeBasisDeformations.Foundations.StandardForm

/-!
# The converse of Corollary 4.15: `A ≅ A₀` implies that `A` is standard

`scalar-normalization.tex:657–662`: "Conversely an isomorphism `A ≅ A₀` gives an equivalence
`F : ind(mod A) → C`, possibly permuting labels. Since `C` is generated in degree one with
homogeneous relations, `gr_J C = C`. Thus `gr F` is a graded automorphism of `C` with the same
permutation. Applying `(gr F)⁻¹` after `F` gives the required object-preserving equivalence."

An isomorphism `ψ : A ≅ A₀` makes the evaluated modules `M_x` of `C = k(Γ_A)` into
indecomposable `A`-modules, which identifies `C` with `ind(mod A)` up to a permutation `σ` of the
labels (`Φ`). Under `Φ` the radical powers of `ind(mod A)` are the morphisms of degree at least
`m` of `C` (`gr_J C = C`, `MeshRadical`). Deviation: instead of correcting `F` by `(gr F)⁻¹`, the
degree-one parts of the arrow representatives are taken as lifts; their mesh errors are of degree
two and lie in `J³`, so they vanish, and the filtered normal form (`Lifts.functor`) gives the
object-preserving equivalence (`isStandard_of_algEquiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The algebra `A₀` of `A`. -/
abbrev A0 := (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ

section Generic

variable {S b} {B : Type w} [Ring B] [Algebra k B] (ψ : B ≃ₐ[k] S.A0 b)

/-- `Bᵐᵒᵖ ≅ Alg F₀`. -/
def eOp : Bᵐᵒᵖ ≃+* CatAlg.Alg (S.arMeshData b).F0 where
  toFun a := (ψ a.unop).unop
  invFun x := MulOpposite.op (ψ.symm (MulOpposite.op x))
  left_inv a := by simp
  right_inv x := by simp
  map_mul' a c := by simp
  map_add' a c := by simp

theorem eOp_algebraMap (t : k) : eOp ψ (algebraMap k Bᵐᵒᵖ t) = algebraMap k _ t := by
  change (ψ (algebraMap k B t)).unop = _
  rw [ψ.commutes]
  rfl

variable (S b) in
/-- The evaluation `C → mod A₀`. -/
def ev : S.ARMeshCategory b ⥤ ModuleCat.{w} (CatAlg.Alg (S.arMeshData b).F0) where
  obj X := ModuleCat.of _ (CatAlg.Rep (S.arMeshData b).F0 X)
  map f := ModuleCat.ofHom (CatAlg.repMap f)
  map_id X := by ext m y; simp
  map_comp f g := by ext m y; simp

/-- The evaluation `C → mod B` through `ψ`. -/
def evA : S.ARMeshCategory b ⥤ RightModuleCat B :=
  ev S b ⋙ ModuleCat.restrictScalars (eOp ψ).toRingHom

theorem evA_map_apply {X Y : S.ARMeshCategory b} (f : X ⟶ Y)
    (m : CatAlg.Rep (S.arMeshData b).F0 X) :
    ((evA ψ).map f).hom m = CatAlg.repMap f m := rfl

/-- The `k`-action on an evaluated `A`-module is the natural one. -/
theorem evA_smul {X : S.ARMeshCategory b} (t : k) (m : CatAlg.Rep (S.arMeshData b).F0 X) :
    (t • (show (evA ψ).obj X from m) : (evA ψ).obj X) =
      (t • m : CatAlg.Rep (S.arMeshData b).F0 X) := by
  change (eOp ψ (algebraMap k Bᵐᵒᵖ t)) • m = _
  rw [eOp_algebraMap, algebraMap_smul]

theorem evA_map_add {X Y : S.ARMeshCategory b} (f g : X ⟶ Y) :
    (evA ψ).map (f + g) = (evA ψ).map f + (evA ψ).map g := by
  ext m
  change CatAlg.repMap (f + g) m = CatAlg.repMap f m + CatAlg.repMap g m
  rw [CatAlg.repMap_add]; rfl

theorem evA_map_sub {X Y : S.ARMeshCategory b} (f g : X ⟶ Y) :
    (evA ψ).map (f - g) = (evA ψ).map f - (evA ψ).map g := by
  rw [eq_sub_iff_add_eq, ← evA_map_add, sub_add_cancel]

theorem evA_map_smul {X Y : S.ARMeshCategory b} (t : k) (f : X ⟶ Y) :
    (evA ψ).map (t • f) = t • (evA ψ).map f := by
  ext m
  change CatAlg.repMap (t • f) m = (t • (show (evA ψ).obj Y from CatAlg.repMap f m) : (evA ψ).obj Y)
  rw [evA_smul, CatAlg.repMap_smul_apply]

theorem evA_map_injective (x y : S.ARVertex) :
    Function.Injective fun f : S.meshObj b x ⟶ S.meshObj b y ↦ (evA ψ).map f := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  intro f g h
  rw [← sub_eq_zero]
  refine (S.arMeshData b).repMap_eq_zero x y (f - g) fun m ↦ ?_
  have := congrArg (fun φ ↦ φ.hom m) h
  simp only [evA_map_apply] at this
  have e : CatAlg.repMap (F := (S.arMeshData b).F0) (f - g) m =
      CatAlg.repMap f m - CatAlg.repMap g m := by
    ext z; simp [Preadditive.comp_sub]
  rw [e, this, sub_self]

theorem evA_map_surjective (x y : S.ARVertex)
    (g : (evA ψ).obj (S.meshObj b x) ⟶ (evA ψ).obj (S.meshObj b y)) :
    ∃ f : S.meshObj b x ⟶ S.meshObj b y, (evA ψ).map f = g := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  let gl : CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b x) →ₗ[CatAlg.Alg (S.arMeshData b).F0]
      CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b y) :=
    { toFun := g.hom
      map_add' := map_add g.hom
      map_smul' := fun a m ↦ by
        obtain ⟨a', rfl⟩ := (eOp ψ).surjective a
        exact g.hom.map_smul a' m }
  obtain ⟨f, hf⟩ := (S.arMeshData b).hom_eq_repMap x y gl
  exact ⟨f, by ext m; exact (hf m).symm⟩

theorem evA_id_ne_zero (x : S.ARVertex) : 𝟙 ((evA ψ).obj (S.meshObj b x)) ≠ 0 := by
  intro h
  apply MeshWalk.id_ne_zero (c := S.arCoefficients b) x
  apply evA_map_injective ψ x x
  simp only
  rw [CategoryTheory.Functor.map_id, h]
  ext m
  change 0 = CatAlg.repMap 0 m
  rw [CatAlg.repMap_zero]; rfl

instance evA_isLocalRing (x : S.ARVertex) : IsLocalRing (End ((evA ψ).obj (S.meshObj b x))) := by
  haveI : Nontrivial (End ((evA ψ).obj (S.meshObj b x))) := ⟨⟨1, 0, evA_id_ne_zero ψ x⟩⟩
  haveI := (S.arLocal b).end_isLocalRing x
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun θ ↦ ?_
  obtain ⟨f, rfl⟩ := evA_map_surjective ψ x x θ
  let f' : End (S.meshObj b x) := f
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := f') (b := 1 - f')
    (add_sub_cancel f' 1) with h | h
  · left
    rw [isUnit_iff_isIso] at h ⊢
    exact Functor.map_isIso _ f
  · right
    rw [isUnit_iff_isIso] at h ⊢
    have h' : IsIso (𝟙 (S.meshObj b x) - f) := h
    have e : 𝟙 ((evA ψ).obj (S.meshObj b x)) - (evA ψ).map f =
        (evA ψ).map (𝟙 (S.meshObj b x) - f) := by
      rw [evA_map_sub, CategoryTheory.Functor.map_id]
    change IsIso (𝟙 ((evA ψ).obj (S.meshObj b x)) - (evA ψ).map f)
    rw [e]
    exact Functor.map_isIso _ _

/-- **The evaluated modules are finite-dimensional indecomposable `A`-modules.** -/
theorem evA_isFiniteIndecomposable (x : S.ARVertex) :
    IsFiniteIndecomposable k B ((evA ψ).obj (S.meshObj b x)) := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : FiniteDimensional k (CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b x)) :=
    inferInstanceAs (FiniteDimensional k (CatAlg.Rep (S.arMeshData b).F0
      ((fun x : S.ARVertex ↦ S.meshObj b x) x)))
  refine ⟨?_, MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _⟩
  let φ : CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b x) →ₗ[k] (evA ψ).obj (S.meshObj b x) :=
    { toFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun t m ↦ (evA_smul ψ t m).symm }
  exact Module.Finite.of_surjective φ fun m ↦ ⟨m, rfl⟩

/-! ### The comparison with a skeleton -/

section Comparison

variable (S' : IndSkeleton k B) (σ : S.ARVertex → Fin S'.n)
  (θ : ∀ x : S.ARVertex, (evA ψ).obj (S.meshObj b x) ≅ S'.obj (σ x))

/-- The comparison `C(x, y) → ind(mod A)(σ x, σ y)`. -/
def Φm {x y : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y) :
    (S'.ind (σ x) : S'.Ind) ⟶ S'.ind (σ y) :=
  InducedCategory.homMk ((θ x).inv ≫ (evA ψ).map f ≫ (θ y).hom)

theorem Φm_hom {x y : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y) :
    (Φm ψ S' σ θ f).hom = (θ x).inv ≫ (evA ψ).map f ≫ (θ y).hom := rfl

theorem Φm_comp {x y z : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y)
    (g : S.meshObj b y ⟶ S.meshObj b z) : Φm ψ S' σ θ (f ≫ g) = Φm ψ S' σ θ f ≫ Φm ψ S' σ θ g := by
  ext1
  simp only [Φm_hom, InducedCategory.comp_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

theorem Φm_id (x : S.ARVertex) : Φm ψ S' σ θ (𝟙 (S.meshObj b x)) = 𝟙 _ := by
  ext1
  simp [Φm_hom]
  rfl

theorem Φm_add {x y : S.ARVertex} (f g : S.meshObj b x ⟶ S.meshObj b y) :
    Φm ψ S' σ θ (f + g) = Φm ψ S' σ θ f + Φm ψ S' σ θ g := by
  ext1
  simp only [Φm_hom, evA_map_add, Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem Φm_sub {x y : S.ARVertex} (f g : S.meshObj b x ⟶ S.meshObj b y) :
    Φm ψ S' σ θ (f - g) = Φm ψ S' σ θ f - Φm ψ S' σ θ g := by
  ext1
  simp only [Φm_hom, evA_map_sub, Preadditive.sub_comp, Preadditive.comp_sub]
  rfl

theorem Φm_smul {x y : S.ARVertex} (t : k) (f : S.meshObj b x ⟶ S.meshObj b y) :
    Φm ψ S' σ θ (t • f) = t • Φm ψ S' σ θ f := by
  ext1
  simp only [Φm_hom, evA_map_smul, Linear.smul_comp, Linear.comp_smul]
  rfl

theorem Φm_zero {x y : S.ARVertex} : Φm ψ S' σ θ (0 : S.meshObj b x ⟶ S.meshObj b y) = 0 := by
  have := Φm_sub ψ S' σ θ (0 : S.meshObj b x ⟶ S.meshObj b y) 0
  rwa [sub_self, sub_self] at this

theorem Φm_sum {x y : S.ARVertex} {ι : Type*} (s : Finset ι) (f : ι → (S.meshObj b x ⟶ S.meshObj b y)) :
    Φm ψ S' σ θ (∑ i ∈ s, f i) = ∑ i ∈ s, Φm ψ S' σ θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Φm_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Φm_add, ih]

theorem Φm_injective {x y : S.ARVertex} :
    Function.Injective (Φm ψ S' σ θ : (S.meshObj b x ⟶ S.meshObj b y) → _) := by
  intro f g h
  apply evA_map_injective ψ x y
  have := congrArg InducedCategory.Hom.hom h
  simp only [Φm_hom] at this
  have := congrArg (fun u ↦ (θ x).hom ≫ u ≫ (θ y).inv) this
  simpa using this

theorem Φm_surjective {x y : S.ARVertex} (h : (S'.ind (σ x) : S'.Ind) ⟶ S'.ind (σ y)) :
    ∃ f : S.meshObj b x ⟶ S.meshObj b y, Φm ψ S' σ θ f = h := by
  obtain ⟨f, hf⟩ := evA_map_surjective ψ x y ((θ x).hom ≫ h.hom ≫ (θ y).inv)
  refine ⟨f, ?_⟩
  ext1
  rw [Φm_hom, hf]
  simp

theorem isIso_Φm_iff {x : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b x) :
    IsIso (Φm ψ S' σ θ f) ↔ IsIso f := by
  constructor
  · intro hi
    obtain ⟨g, hg⟩ := Φm_surjective ψ S' σ θ (inv (Φm ψ S' σ θ f))
    refine ⟨g, Φm_injective ψ S' σ θ ?_, Φm_injective ψ S' σ θ ?_⟩
    · rw [Φm_comp, hg, IsIso.hom_inv_id, Φm_id]
    · rw [Φm_comp, hg, IsIso.inv_hom_id, Φm_id]
  · intro hi
    refine ⟨Φm ψ S' σ θ (inv f), ?_, ?_⟩
    · rw [← Φm_comp, IsIso.hom_inv_id, Φm_id]
    · rw [← Φm_comp, IsIso.inv_hom_id, Φm_id]

variable [Finite S.ARVertex]

include θ in
theorem σ_injective : Function.Injective σ := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  intro x y h
  have u : (evA ψ).obj (S.meshObj b x) ≅ (evA ψ).obj (S.meshObj b y) :=
    θ x ≪≫ eqToIso (congrArg S'.obj h) ≪≫ (θ y).symm
  obtain ⟨f, hf⟩ := evA_map_surjective ψ x y u.hom
  obtain ⟨g, hg⟩ := evA_map_surjective ψ y x u.inv
  refine MeshWalk.eq_of_comp_eq_id (c := S.arCoefficients b)
    (fun x y ↦ S.finiteDimensional_meshHom b x y) f g (evA_map_injective ψ x x ?_)
  simp only
  rw [Functor.map_comp, hf, hg, Iso.hom_inv_id, CategoryTheory.Functor.map_id]



/-! ### Radical powers are degrees -/

theorem isRadical_Φm_iff {x y : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y) :
    S'.IsRadical (Φm ψ S' σ θ f) ↔ ScalarMeshCategory.degProj (S.arCoefficients b) 0 x y f = 0 := by
  rw [← MeshWalk.radical_iff (c := S.arCoefficients b) (fun x y ↦ S.finiteDimensional_meshHom b x y)]
  constructor
  · intro h g
    have := h (Φm ψ S' σ θ g)
    rwa [← Φm_comp, ← Φm_id, ← Φm_sub, isIso_Φm_iff] at this
  · intro h g
    obtain ⟨g', rfl⟩ := Φm_surjective ψ S' σ θ g
    rw [← Φm_comp, ← Φm_id, ← Φm_sub, isIso_Φm_iff]
    exact h g'

theorem path_first {V : Type} [Quiver.{0} V] {x y : V} (p : Quiver.Path x y) (hp : 0 < p.length) :
    ∃ (z : V) (a : x ⟶ z) (p' : Quiver.Path z y), p = a.toPath.comp p' ∧ p'.length + 1 = p.length := by
  induction p with
  | nil => simp at hp
  | cons q a ih =>
    by_cases hq : q.length = 0
    · obtain rfl := Quiver.Path.eq_of_length_zero q hq
      cases Quiver.Path.eq_nil_of_length_zero q hq
      exact ⟨_, a, Quiver.Path.nil, rfl, by simp⟩
    · obtain ⟨z, a', p', rfl, hl⟩ := ih (by omega)
      exact ⟨z, a', p'.cons a, by rw [Quiver.Path.comp_cons], by simp [hl]⟩

variable {σ} in
/-- **Under `Φ`, the radical powers are the morphisms of degree at least `m`.** -/
theorem mem_radPow_Φm_iff (hσ : Function.Bijective σ) (m : ℕ) {x y : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y) :
    Φm ψ S' σ θ f ∈ S'.radPow m _ _ ↔ MeshWalk.Ge (S.arCoefficients b) m f := by
  have hfin : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  constructor
  · induction m generalizing x y f with
    | zero => intro _; exact MeshWalk.ge_zero f
    | succ m ih =>
      intro hf
      suffices H : ∀ h ∈ S'.radPow (m + 1) (S'.ind (σ x)) (S'.ind (σ y)),
          ∀ f₀ : S.meshObj b x ⟶ S.meshObj b y, Φm ψ S' σ θ f₀ = h →
            MeshWalk.Ge (S.arCoefficients b) (m + 1) f₀ from H _ hf f rfl
      intro h hh
      induction hh using Submodule.span_induction with
      | mem h hh =>
        obtain ⟨Z, f', g', hf', hg', rfl⟩ := hh
        obtain ⟨z, rfl⟩ := hσ.2 Z
        obtain ⟨φ, rfl⟩ := Φm_surjective ψ S' σ θ f'
        obtain ⟨γ, rfl⟩ := Φm_surjective ψ S' σ θ g'
        intro f₀ hf₀
        rw [← Φm_comp] at hf₀
        obtain rfl := Φm_injective ψ S' σ θ hf₀
        have h1 : MeshWalk.Ge (S.arCoefficients b) 1 φ := fun d hd ↦ by
          obtain rfl : d = 0 := by omega
          exact (isRadical_Φm_iff ψ S' σ θ φ).1 hf'
        have := MeshWalk.ge_comp hfin h1 (ih γ hg')
        rwa [add_comm] at this
      | zero =>
        intro f₀ hf₀
        rw [← Φm_zero (x := x) (y := y) ψ S' σ θ] at hf₀
        obtain rfl := Φm_injective ψ S' σ θ hf₀
        exact MeshWalk.ge_zero_mor _
      | add h₁ h₂ _ _ ih₁ ih₂ =>
        intro f₀ hf₀
        obtain ⟨f₁, rfl⟩ := Φm_surjective ψ S' σ θ h₁
        obtain ⟨f₂, rfl⟩ := Φm_surjective ψ S' σ θ h₂
        rw [← Φm_add] at hf₀
        obtain rfl := Φm_injective ψ S' σ θ hf₀
        exact (ih₁ f₁ rfl).add (ih₂ f₂ rfl)
      | smul t h₁ _ ih₁ =>
        intro f₀ hf₀
        obtain ⟨f₁, rfl⟩ := Φm_surjective ψ S' σ θ h₁
        rw [← Φm_smul] at hf₀
        obtain rfl := Φm_injective ψ S' σ θ hf₀
        exact (ih₁ f₁ rfl).smul t
  · induction m generalizing x y f with
    | zero => intro _; trivial
    | succ m ih =>
      intro hf
      have hpath : ∀ (d : ℕ), m + 1 ≤ d → ∀ (p : Quiver.Path x y), p.length = d →
          Φm ψ S' σ θ (ScalarMeshCategory.pathMor (S.arCoefficients b) p) ∈
            S'.radPow (m + 1) (S'.ind (σ x)) (S'.ind (σ y)) := by
        intro d hd p hp
        obtain ⟨z, a, p', rfl, hl⟩ := path_first p (by omega)
        rw [ScalarMeshCategory.pathMor_comp, ScalarMeshCategory.pathMor_toPath, Φm_comp]
        refine Submodule.subset_span ⟨_, _, _, ?_, ih _ ?_, rfl⟩
        · rw [isRadical_Φm_iff, ← ScalarMeshCategory.pathMor_toPath,
            ScalarMeshCategory.degProj_of_mem _
              (ScalarMeshCategory.pathMor_mem_degreePart (S.arCoefficients b) a.toPath)]
          simp
        · exact MeshWalk.ge_of_mem (ScalarMeshCategory.pathMor_mem_degreePart _ p') (by omega)
      obtain ⟨N, hN⟩ := ScalarMeshCategory.exists_degreePart_eq_bot (S.arCoefficients b) hfin
      rw [ScalarMeshCategory.eq_sum_degProj _ hN f, Φm_sum]
      refine Submodule.sum_mem _ fun d hd ↦ ?_
      by_cases hdm : d < m + 1
      · rw [hf d hdm, Φm_zero]; exact Submodule.zero_mem _
      have hmem := ScalarMeshCategory.degProj_mem (S.arCoefficients b) d f
      rw [ScalarMeshCategory.degreePart_eq_span] at hmem
      generalize ScalarMeshCategory.degProj (S.arCoefficients b) d x y f = g at hmem ⊢
      induction hmem using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨p, hp, rfl⟩ := hg
        exact hpath d (by omega) p hp
      | zero => rw [Φm_zero]; exact Submodule.zero_mem _
      | add g₁ g₂ _ _ h₁ h₂ => rw [Φm_add]; exact Submodule.add_mem _ h₁ h₂
      | smul t g _ h₁ => rw [Φm_smul]; exact Submodule.smul_mem _ t h₁

end Comparison

end Generic

/-! ### The relabelling of `ind(mod A)` -/

section Relabel

variable {S b} (ψ : A ≃ₐ[k] S.A0 b)

/-- The label of the evaluated module of `x`. -/
def σl (x : S.ARVertex) : Fin S.n :=
  Classical.choose (S.complete _ (evA_isFiniteIndecomposable ψ x))

/-- `M_x ≅ X_{σ x}`. -/
def θl (x : S.ARVertex) : (evA ψ).obj (S.meshObj b x) ≅ S.obj (σl ψ x) :=
  (Classical.choose_spec (S.complete _ (evA_isFiniteIndecomposable ψ x))).some

variable [Finite S.ARVertex]

theorem σl_bijective : Function.Bijective (σl ψ) :=
  (Finite.injective_iff_bijective).1 (σ_injective ψ S (σl ψ) (θl ψ))

/-! ### Degree-one lifts and standardness -/

/-- The relabelling as an equivalence. -/
def σe : S.ARVertex ≃ Fin S.n := Equiv.ofBijective (σl ψ) (σl_bijective ψ)

theorem τl (v : S.ARVertex) : S.ind (σl ψ ((σe ψ).symm v)) = S.label v := by
  change σl ψ ((σe ψ).symm v) = v
  exact (σe ψ).apply_symm_apply v

/-- Transport along the relabelling. -/
def cv {v w : S.ARVertex} (h : S.ind (σl ψ ((σe ψ).symm v)) ⟶ S.ind (σl ψ ((σe ψ).symm w))) :
    S.label v ⟶ S.label w :=
  eqToHom (τl ψ v).symm ≫ h ≫ eqToHom (τl ψ w)

theorem cv_comp {u v w : S.ARVertex} (h : S.ind (σl ψ ((σe ψ).symm u)) ⟶ S.ind (σl ψ ((σe ψ).symm v)))
    (h' : S.ind (σl ψ ((σe ψ).symm v)) ⟶ S.ind (σl ψ ((σe ψ).symm w))) :
    cv ψ h ≫ cv ψ h' = cv ψ (h ≫ h') := by
  simp [cv]

theorem cv_sub {v w : S.ARVertex} (h h' : S.ind (σl ψ ((σe ψ).symm v)) ⟶ S.ind (σl ψ ((σe ψ).symm w))) :
    cv ψ (h - h') = cv ψ h - cv ψ h' := by
  simp [cv, Preadditive.comp_sub, Preadditive.sub_comp]

theorem cv_smul {v w : S.ARVertex} (t : k)
    (h : S.ind (σl ψ ((σe ψ).symm v)) ⟶ S.ind (σl ψ ((σe ψ).symm w))) :
    cv ψ (t • h) = t • cv ψ h := by
  simp [cv, Linear.comp_smul, Linear.smul_comp]

theorem cv_sum {v w : S.ARVertex} {ι : Type*} (s : Finset ι)
    (h : ι → (S.ind (σl ψ ((σe ψ).symm v)) ⟶ S.ind (σl ψ ((σe ψ).symm w)))) :
    cv ψ (∑ i ∈ s, h i) = ∑ i ∈ s, cv ψ (h i) := by
  simp [cv, Preadditive.comp_sum, Preadditive.sum_comp]

theorem cv_zero {v w : S.ARVertex} :
    cv ψ (0 : S.ind (σl ψ ((σe ψ).symm v)) ⟶ S.ind (σl ψ ((σe ψ).symm w))) = 0 := by
  simp [cv]

theorem mem_radPow_cv_iff (m : ℕ) {v w : S.ARVertex}
    (h : S.ind (σl ψ ((σe ψ).symm v)) ⟶ S.ind (σl ψ ((σe ψ).symm w))) :
    cv ψ h ∈ S.radPow m (S.label v) (S.label w) ↔ h ∈ S.radPow m _ _ := by
  have key : ∀ {X X' Y Y' : S.Ind} (h1 : X = X') (h2 : Y = Y') (f : X ⟶ Y),
      eqToHom h1.symm ≫ f ≫ eqToHom h2 ∈ S.radPow m X' Y' ↔ f ∈ S.radPow m X Y := by
    intro X X' Y Y' h1 h2 f
    subst h1 h2
    simp
  exact key (τl ψ v) (τl ψ w) h

theorem exists_cv_Φm {v w : S.ARVertex} (h : S.label v ⟶ S.label w) :
    ∃ g : S.meshObj b ((σe ψ).symm v) ⟶ S.meshObj b ((σe ψ).symm w), cv ψ (Φm ψ S (σl ψ) (θl ψ) g) = h := by
  obtain ⟨g, hg⟩ := Φm_surjective ψ S (σl ψ) (θl ψ) (eqToHom (τl ψ v) ≫ h ≫ eqToHom (τl ψ w).symm)
  exact ⟨g, by simp [cv, hg]⟩

/-- The arrow representatives read in `C`. -/
def repC {v w : S.ARVertex} (a : v ⟶ w) : S.meshObj b ((σe ψ).symm v) ⟶ S.meshObj b ((σe ψ).symm w) :=
  Classical.choose (exists_cv_Φm ψ (S.rep b a))

theorem cv_repC {v w : S.ARVertex} (a : v ⟶ w) : cv ψ (Φm ψ S (σl ψ) (θl ψ) (repC ψ a)) = S.rep b a :=
  Classical.choose_spec (exists_cv_Φm ψ (S.rep b a))

/-- **The degree-one lifts.** -/
def liftsC : S.Lifts b where
  L a := cv ψ (Φm ψ S (σl ψ) (θl ψ) (ScalarMeshCategory.degProj (S.arCoefficients b) 1 _ _ (repC ψ a)))
  sub_mem a := by
    rw [← cv_repC ψ a, ← cv_sub, mem_radPow_cv_iff, ← Φm_sub, mem_radPow_Φm_iff ψ S (θl ψ) (σl_bijective ψ)]
    have h1 : MeshWalk.Ge (S.arCoefficients b) 1 (repC ψ a) := by
      rw [← mem_radPow_Φm_iff ψ S (θl ψ) (σl_bijective ψ), ← mem_radPow_cv_iff, cv_repC]
      exact S.rep_mem b a
    intro d hd
    rw [map_sub]
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · rw [ScalarMeshCategory.degProj_of_mem _ (ScalarMeshCategory.degProj_mem _ 1 _), if_neg (by omega),
        h1 0 (by omega), sub_zero]
    · rw [ScalarMeshCategory.degProj_of_mem _ (ScalarMeshCategory.degProj_mem _ 1 _), if_pos rfl,
        sub_self]

/-- The mesh error of the degree-one lifts, read in `C`: homogeneous of degree two. -/
def errC (x : S.nonprojectiveVertices) :
    S.meshObj b ((σe ψ).symm (S.arTranslationQuiver.tau x).1) ⟶ S.meshObj b ((σe ψ).symm x.1) :=
  ∑ a : Σ y : S.ARVertex, y ⟶ x.1, ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
    (ScalarMeshCategory.degProj (S.arCoefficients b) 1 _ _
        (repC ψ (S.arTranslationQuiver.mate x a.1 a.2)) ≫
      ScalarMeshCategory.degProj (S.arCoefficients b) 1 _ _ (repC ψ a.2))

theorem error_liftsC (x : S.nonprojectiveVertices) :
    (liftsC ψ).error x = cv ψ (Φm ψ S (σl ψ) (θl ψ) (errC ψ x)) := by
  rw [Lifts.error_eq, errC, Φm_sum, cv_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Φm_smul, cv_smul, Φm_comp, ← cv_comp]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The mesh errors of the degree-one lifts vanish.** -/
theorem error_liftsC_eq_zero (x : S.nonprojectiveVertices) : (liftsC ψ).error x = 0 := by
  have h3 := (liftsC ψ).error_mem_three x
  rw [error_liftsC, mem_radPow_cv_iff, mem_radPow_Φm_iff ψ S (θl ψ) (σl_bijective ψ)] at h3
  have hE2 : errC ψ x ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) (1 + 1) _ _ :=
    Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
      (ScalarMeshCategory.comp_mem_degreePart' _ (ScalarMeshCategory.degProj_mem _ 1 _)
        (ScalarMeshCategory.degProj_mem _ 1 _))
  have h0 : errC ψ x = 0 := by
    have := h3 (1 + 1) (by omega)
    rwa [ScalarMeshCategory.degProj_of_mem _ hE2, if_pos rfl] at this
  rw [error_liftsC, h0, Φm_zero, cv_zero]

include ψ in
/-- **The converse of Corollary 4.15** (`cor:graded-standard-form`): if `A ≅ A₀`, then `A` is
standard. -/
theorem isStandard_of_algEquiv' : S.IsStandard :=
  ⟨b, (liftsC ψ).functor (error_liftsC_eq_zero ψ),
    (liftsC ψ).functor_isEquivalence (error_liftsC_eq_zero ψ),
    (liftsC ψ).functor_isLinear (error_liftsC_eq_zero ψ), fun _ ↦ ⟨Iso.refl _⟩⟩

end Relabel

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w'

variable {k A : Type w'} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **The converse of Corollary 4.15** (`cor:graded-standard-form`): if `A ≅ A₀`, then `A` is
standard. -/
theorem isStandard_of_algEquiv (ψ : A ≃ₐ[k] S.A0 b) : S.IsStandard := by
  haveI : Finite S.ARVertex := inferInstanceAs (Finite (Fin S.n))
  exact isStandard_of_algEquiv' ψ

end MultiplicativeBasisDeformations.IndSkeleton
