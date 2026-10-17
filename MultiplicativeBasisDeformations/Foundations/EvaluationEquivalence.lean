import MultiplicativeBasisDeformations.Foundations.A0RepFinite

/-!
# Proposition 2.10(1): evaluation is an equivalence `add C ≃ mod A₀`

`prop:projective-evaluation`(1) (`graded-category.tex`): "Evaluation induces an equivalence
`add C ≃ mod A₀`."

`add C` is the category of finite families of labels with matrices of morphisms (`AddC`), and
`mod A₀` the full subcategory of finitely generated modules over the category algebra of the
projective labels (`ModFG`). Evaluation is a functor (`evFunctor`); it is faithful
(`evMap_injective`), full (`evMap_surjective`) and essentially surjective (`InjData.essSurj`), hence
an equivalence (`evFunctor_isEquivalence`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}

set_option linter.unusedVariables false in
/-- **`add C`**: finite families of labels, with matrices of morphisms. -/
structure AddC (F : ι → 𝒞) where
  n : ℕ
  Z : Fin n → ι

namespace AddC

/-- The identity matrix. -/
def idMat (X : AddC F) : ∀ j j' : Fin X.n, F (X.Z j) ⟶ F (X.Z j') :=
  fun j j' ↦ if h : j = j' then eqToHom (by rw [h]) else 0

instance : Category (AddC F) where
  Hom X Y := ∀ j j', F (X.Z j) ⟶ F (Y.Z j')
  id X := idMat X
  comp f g := fun j j'' ↦ ∑ j', f j j' ≫ g j' j''
  id_comp f := by
    funext j j''
    rw [Finset.sum_eq_single j (fun j' _ hj ↦ by simp [idMat, Ne.symm hj])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp [idMat]
  comp_id f := by
    funext j j''
    rw [Finset.sum_eq_single j'' (fun j' _ hj ↦ by simp [idMat, hj])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp [idMat]
  assoc f g h := by
    funext j j'''
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    exact Finset.sum_comm

theorem comp_apply {X Y Z : AddC F} (f : X ⟶ Y) (g : Y ⟶ Z) (j : Fin X.n) (j'' : Fin Z.n) :
    (f ≫ g) j j'' = ∑ j', f j j' ≫ g j' j'' := rfl

theorem id_apply (X : AddC F) (j j' : Fin X.n) :
    (𝟙 X : X ⟶ X) j j' = if h : j = j' then eqToHom (by rw [h]) else 0 := rfl

end AddC

namespace MeshData

variable {L : LocalFamily (k := k) F} (D : MeshData F L)

/-- **`mod A₀`**: finitely generated modules over the category algebra of the projective labels. -/
abbrev ModFG := ObjectProperty.FullSubcategory fun X : ModuleCat.{w} (Alg D.F0) ↦
  Module.Finite (Alg D.F0) X

theorem repMap_id' (X : 𝒞) (m : Rep D.F0 X) : repMap (F := D.F0) (𝟙 X) m = m := by
  funext y; exact Category.comp_id _

theorem repMap_neg' {X Y : 𝒞} (g : X ⟶ Y) : repMap (F := D.F0) (-g) = -repMap g := by
  have h := repMap_add (F := D.F0) g (-g)
  rw [add_neg_cancel, repMap_zero] at h
  exact (eq_neg_of_add_eq_zero_right h.symm)

theorem evMap_sub {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {Z : κ → ι} {Z' : κ' → ι} (f g : Mat F Z Z') : D.evMap (f - g) = D.evMap f - D.evMap g := by
  refine LinearMap.ext fun m ↦ funext fun j' ↦ ?_
  simp only [evMap_apply, LinearMap.sub_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [sub_eq_add_neg, repMap_add, repMap_neg', LinearMap.add_apply, LinearMap.neg_apply,
    ← sub_eq_add_neg]

/-- **Evaluation** `add C → Mod A₀`. -/
def evFunctor0 : AddC F ⥤ ModuleCat.{w} (Alg D.F0) where
  obj X := ModuleCat.of (Alg D.F0) (D.EZ X.Z)
  map f := ModuleCat.ofHom (D.evMap f)
  map_id X := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun m ↦ funext fun j' ↦ ?_
    change D.evMap (AddC.idMat X) m j' = m j'
    rw [evMap_apply, Finset.sum_eq_single j' (fun j _ hj ↦ by simp [AddC.idMat, hj, repMap_zero])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp only [AddC.idMat, dif_pos, eqToHom_refl]
    exact repMap_id' D _ _
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun m ↦ funext fun j'' ↦ ?_
    change D.evMap (fun j j'' ↦ ∑ j', f j j' ≫ g j' j'') m j'' =
      D.evMap g (D.evMap f m) j''
    simp only [evMap_apply, repMap_sum, LinearMap.sum_apply, repMap_comp, LinearMap.comp_apply,
      map_sum]
    exact Finset.sum_comm

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

instance : (evFunctor0 D).Faithful where
  map_injective {X Y} f g h := by
    have h' : D.evMap (f : Mat F X.Z Y.Z) = D.evMap (g : Mat F X.Z Y.Z) :=
      congrArg ModuleCat.Hom.hom h
    let f' : Mat F X.Z Y.Z := f
    let g' : Mat F X.Z Y.Z := g
    have := D.evMap_injective (f := f' - g') (by rw [evMap_sub, h', sub_self])
    have h2 : f' = g' := sub_eq_zero.1 this
    exact h2

instance : (evFunctor0 D).Full where
  map_surjective {X Y} g := by
    obtain ⟨f, hf⟩ := D.evMap_surjective (Z := X.Z) (Z' := Y.Z) g.hom
    exact ⟨f, ModuleCat.hom_ext hf⟩

theorem evZ_finite (X : AddC F) : Module.Finite (Alg D.F0) (D.EZ X.Z) :=
  Module.Finite.of_restrictScalars_finite k _ _

/-- **Evaluation** `add C → mod A₀`. -/
abbrev evFunctor : AddC F ⥤ ModFG D :=
  ObjectProperty.lift _ (evFunctor0 D) fun X ↦ evZ_finite D X

variable (J : InjData D)

instance : (evFunctor D).Faithful :=
  Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ (evFunctor0 D) _)

instance : (evFunctor D).Full :=
  Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ (evFunctor0 D) _)

include J in
theorem evFunctor_essSurj : (evFunctor D).EssSurj where
  mem_essImage Y := by
    obtain ⟨Yo, hY⟩ := Y
    let _ : Module k Yo := Module.compHom Yo (algebraMap k (Alg D.F0))
    have : IsScalarTower k (Alg D.F0) Yo :=
      ⟨fun c a y ↦ by
        change (c • a) • y = algebraMap k (Alg D.F0) c • (a • y)
        rw [Algebra.smul_def, mul_smul]⟩
    have : FiniteDimensional k Yo := Module.Finite.trans (Alg D.F0) Yo
    obtain ⟨μ, _, _, W, ⟨e⟩⟩ := J.essSurj (X := Yo)
    let eμ := Fintype.equivFin μ
    let e' : Yo ≃ₗ[Alg D.F0] D.EZ (fun i ↦ W (eμ.symm i)) :=
      e.trans (LinearEquiv.piCongrLeft' (Alg D.F0) (fun j ↦ Rep D.F0 (F (W j))) eμ)
    refine ⟨⟨Fintype.card μ, fun i ↦ W (eμ.symm i)⟩, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact e'.symm.toModuleIso ≪≫ eqToIso (ModuleCat.of_coe (R := Alg D.F0) Yo)

include J in
/-- **Proposition 2.10(1)** (`prop:projective-evaluation`(1)): evaluation is an equivalence
`add C ≃ mod A₀`. -/
theorem evFunctor_isEquivalence : (evFunctor D).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := evFunctor_essSurj D J

/-! ### Transport along a ring isomorphism -/

section Transport

variable {R' : Type w} [Ring R']

/-- Finitely generated modules over a ring. -/
abbrev FGProp (R' : Type w) [Ring R'] : ObjectProperty (ModuleCat.{w} R') :=
  fun X ↦ Module.Finite R' X

instance : (FGProp R').IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have : Module.Finite R' X := hX
    exact Module.Finite.equiv e.toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem finite_compHom_iff {A : Type*} [Ring A] (r : R' ≃+* A) (X : Type*) [AddCommGroup X]
    [Module A X] :
    (letI : Module R' X := Module.compHom X r.toRingHom; Module.Finite R' X) ↔ Module.Finite A X := by
  letI : Module R' X := Module.compHom X r.toRingHom
  have hsm : ∀ (c : R') (x : X), c • x = r c • x := fun _ _ ↦ rfl
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨⟨S, eq_top_iff.2 fun x hxt ↦ ?_⟩⟩
    clear hxt
    have hx : x ∈ Submodule.span R' (S : Set X) := by rw [hS]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy => rw [hsm]; exact Submodule.smul_mem _ _ hy
  · rintro ⟨S, hS⟩
    refine ⟨⟨S, eq_top_iff.2 fun x hxt ↦ ?_⟩⟩
    clear hxt
    have hx : x ∈ Submodule.span A (S : Set X) := by rw [hS]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
        have : a • y = r.symm a • y := by rw [hsm, RingEquiv.apply_symm_apply]
        rw [this]; exact Submodule.smul_mem _ _ hy

theorem fg_restrictScalars_iff (r : R' ≃+* Alg D.F0) (X : ModuleCat.{w} (Alg D.F0)) :
    Module.Finite R' ((ModuleCat.restrictScalars r.toRingHom).obj X) ↔
      Module.Finite (Alg D.F0) X :=
  finite_compHom_iff r X

/-- **`add C ≃ mod R'`** for any ring `R'` isomorphic to the category algebra of the projective
labels (for instance `kP` on the other side of `A₀ ≅ kP`). -/
def evEquivOfRingEquiv (J : InjData D) (r : R' ≃+* Alg D.F0) :
    AddC F ≌ (FGProp R').FullSubcategory :=
  haveI := evFunctor_isEquivalence D J
  (evFunctor D).asEquivalence.trans
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv r).congrFullSubcategory (by
      funext X
      exact propext (fg_restrictScalars_iff D r X)))

end Transport

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
